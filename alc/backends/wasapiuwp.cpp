/**
 * OpenAL cross platform audio library
 * Copyright (C) 2011 by authors.
 * This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Library General Public
 *  License as published by the Free Software Foundation; either
 *  version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public
 *  License along with this library; if not, write to the
 *  Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 * Or go to http://www.gnu.org/copyleft/lgpl.html
 */

#include "config.h"

#include "backends/wasapiuwp.h"

#define WIN32_LEAN_AND_MEAN
#include <windows.h>

#include <wrl\implements.h>
#include <mfapi.h>

#include <stdlib.h>
#include <stdio.h>
#include <memory.h>

#include <wtypes.h>
#include <mmdeviceapi.h>
#include <audioclient.h>
#include <cguid.h>
#include <devpropdef.h>
#include <mmreg.h>
#include <propsys.h>
#include <propkey.h>
#include <devpkey.h>
#ifndef _WAVEFORMATEXTENSIBLE_
#include <ks.h>
#include <ksmedia.h>
#endif

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <deque>
#include <functional>
#include <future>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#include "alcmain.h"
#include "alexcpt.h"
#include "alu.h"
#include "compat.h"
#include "converter.h"
#include "logging.h"
#include "ringbuffer.h"
#include "strutils.h"
#include "threads.h"


/* Some headers seem to define these as macros for __uuidof, which is annoying
 * since some headers don't declare them at all. Hopefully the ifdef is enough
 * to tell if they need to be declared.
 */
#ifndef KSDATAFORMAT_SUBTYPE_PCM
DEFINE_GUID(KSDATAFORMAT_SUBTYPE_PCM, 0x00000001, 0x0000, 0x0010, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71);
#endif
#ifndef KSDATAFORMAT_SUBTYPE_IEEE_FLOAT
DEFINE_GUID(KSDATAFORMAT_SUBTYPE_IEEE_FLOAT, 0x00000003, 0x0000, 0x0010, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71);
#endif


namespace {

using std::chrono::milliseconds;
using std::chrono::seconds;

using ReferenceTime = std::chrono::duration<REFERENCE_TIME,std::ratio<1,10000000>>;

inline constexpr ReferenceTime operator "" _reftime(unsigned long long int n) noexcept
{ return ReferenceTime{static_cast<REFERENCE_TIME>(n)}; }


#define MONO SPEAKER_FRONT_CENTER
#define STEREO (SPEAKER_FRONT_LEFT|SPEAKER_FRONT_RIGHT)
#define QUAD (SPEAKER_FRONT_LEFT|SPEAKER_FRONT_RIGHT|SPEAKER_BACK_LEFT|SPEAKER_BACK_RIGHT)
#define X5DOT1 (SPEAKER_FRONT_LEFT|SPEAKER_FRONT_RIGHT|SPEAKER_FRONT_CENTER|SPEAKER_LOW_FREQUENCY|SPEAKER_SIDE_LEFT|SPEAKER_SIDE_RIGHT)
#define X5DOT1REAR (SPEAKER_FRONT_LEFT|SPEAKER_FRONT_RIGHT|SPEAKER_FRONT_CENTER|SPEAKER_LOW_FREQUENCY|SPEAKER_BACK_LEFT|SPEAKER_BACK_RIGHT)
#define X6DOT1 (SPEAKER_FRONT_LEFT|SPEAKER_FRONT_RIGHT|SPEAKER_FRONT_CENTER|SPEAKER_LOW_FREQUENCY|SPEAKER_BACK_CENTER|SPEAKER_SIDE_LEFT|SPEAKER_SIDE_RIGHT)
#define X7DOT1 (SPEAKER_FRONT_LEFT|SPEAKER_FRONT_RIGHT|SPEAKER_FRONT_CENTER|SPEAKER_LOW_FREQUENCY|SPEAKER_BACK_LEFT|SPEAKER_BACK_RIGHT|SPEAKER_SIDE_LEFT|SPEAKER_SIDE_RIGHT)

constexpr inline DWORD MaskFromTopBits(DWORD b) noexcept
{
    b |= b>>1;
    b |= b>>2;
    b |= b>>4;
    b |= b>>8;
    b |= b>>16;
    return b;
}
constexpr DWORD MonoMask{MaskFromTopBits(MONO)};
constexpr DWORD StereoMask{MaskFromTopBits(STEREO)};
constexpr DWORD QuadMask{MaskFromTopBits(QUAD)};
constexpr DWORD X51Mask{MaskFromTopBits(X5DOT1)};
constexpr DWORD X51RearMask{MaskFromTopBits(X5DOT1REAR)};
constexpr DWORD X61Mask{MaskFromTopBits(X6DOT1)};
constexpr DWORD X71Mask{MaskFromTopBits(X7DOT1)};

#define DEVNAME_HEAD "OpenAL Soft on "


/* Scales the given reftime value, ceiling the result. */
inline ALuint RefTime2Samples(const ReferenceTime &val, ALuint srate)
{
    const auto retval = (val*srate + (seconds{1}-1_reftime)) / seconds{1};
    return static_cast<ALuint>(retval);
}


class GuidPrinter {
    char mMsg[64];

public:
    GuidPrinter(const GUID &guid)
    {
        std::snprintf(mMsg, al::size(mMsg), "{%08lx-%04x-%04x-%02x%02x-%02x%02x%02x%02x%02x%02x}",
            DWORD{guid.Data1}, guid.Data2, guid.Data3, guid.Data4[0], guid.Data4[1], guid.Data4[2],
            guid.Data4[3], guid.Data4[4], guid.Data4[5], guid.Data4[6], guid.Data4[7]);
    }
    const char *c_str() const { return mMsg; }
};



bool MakeExtensible(WAVEFORMATEXTENSIBLE *out, const WAVEFORMATEX *in)
{
    *out = WAVEFORMATEXTENSIBLE{};
    if(in->wFormatTag == WAVE_FORMAT_EXTENSIBLE)
    {
        *out = *CONTAINING_RECORD(in, const WAVEFORMATEXTENSIBLE, Format);
        out->Format.cbSize = sizeof(*out) - sizeof(out->Format);
    }
    else if(in->wFormatTag == WAVE_FORMAT_PCM)
    {
        out->Format = *in;
        out->Format.cbSize = 0;
        out->Samples.wValidBitsPerSample = out->Format.wBitsPerSample;
        if(out->Format.nChannels == 1)
            out->dwChannelMask = MONO;
        else if(out->Format.nChannels == 2)
            out->dwChannelMask = STEREO;
        else
            ERR("Unhandled PCM channel count: %d\n", out->Format.nChannels);
        out->SubFormat = KSDATAFORMAT_SUBTYPE_PCM;
    }
    else if(in->wFormatTag == WAVE_FORMAT_IEEE_FLOAT)
    {
        out->Format = *in;
        out->Format.cbSize = 0;
        out->Samples.wValidBitsPerSample = out->Format.wBitsPerSample;
        if(out->Format.nChannels == 1)
            out->dwChannelMask = MONO;
        else if(out->Format.nChannels == 2)
            out->dwChannelMask = STEREO;
        else
            ERR("Unhandled IEEE float channel count: %d\n", out->Format.nChannels);
        out->SubFormat = KSDATAFORMAT_SUBTYPE_IEEE_FLOAT;
    }
    else
    {
        ERR("Unhandled format tag: 0x%04x\n", in->wFormatTag);
        return false;
    }
    return true;
}

void TraceFormat(const char *msg, const WAVEFORMATEX *format)
{
    constexpr size_t fmtex_extra_size{sizeof(WAVEFORMATEXTENSIBLE)-sizeof(WAVEFORMATEX)};
    if(format->wFormatTag == WAVE_FORMAT_EXTENSIBLE && format->cbSize >= fmtex_extra_size)
    {
        const WAVEFORMATEXTENSIBLE *fmtex{
            CONTAINING_RECORD(format, const WAVEFORMATEXTENSIBLE, Format)};
        TRACE("%s:\n"
            "    FormatTag      = 0x%04x\n"
            "    Channels       = %d\n"
            "    SamplesPerSec  = %lu\n"
            "    AvgBytesPerSec = %lu\n"
            "    BlockAlign     = %d\n"
            "    BitsPerSample  = %d\n"
            "    Size           = %d\n"
            "    Samples        = %d\n"
            "    ChannelMask    = 0x%lx\n"
            "    SubFormat      = %s\n",
            msg, fmtex->Format.wFormatTag, fmtex->Format.nChannels, fmtex->Format.nSamplesPerSec,
            fmtex->Format.nAvgBytesPerSec, fmtex->Format.nBlockAlign, fmtex->Format.wBitsPerSample,
            fmtex->Format.cbSize, fmtex->Samples.wReserved, fmtex->dwChannelMask,
            GuidPrinter{fmtex->SubFormat}.c_str());
    }
    else
        TRACE("%s:\n"
            "    FormatTag      = 0x%04x\n"
            "    Channels       = %d\n"
            "    SamplesPerSec  = %lu\n"
            "    AvgBytesPerSec = %lu\n"
            "    BlockAlign     = %d\n"
            "    BitsPerSample  = %d\n"
            "    Size           = %d\n",
            msg, format->wFormatTag, format->nChannels, format->nSamplesPerSec,
            format->nAvgBytesPerSec, format->nBlockAlign, format->wBitsPerSample, format->cbSize);
}


using namespace Microsoft::WRL;
using namespace Windows::Media::Devices;
using namespace Windows::Storage::Streams;


struct WasapiPlayback final : public RuntimeClass< RuntimeClassFlags< ClassicCom >, FtmBase, IActivateAudioInterfaceCompletionHandler >, 
                              public BackendBase {
    WasapiPlayback(ALCdevice *device) noexcept : BackendBase{device} { }
    ~WasapiPlayback() override;

    void close();

    int mixerProc();

    void open(const ALCchar *name) override;

    // IActivateAudioInterfaceCompletionHandler
    STDMETHOD(ActivateCompleted)(IActivateAudioInterfaceAsyncOperation *operation);

    bool reset() override;
    void start() override;
    void stop() override;

    ClockLatency getClockLatency() override;

    std::wstring mDevId;

    IAudioClient *mClient{nullptr};
    IAudioRenderClient *mRender{nullptr};
    HANDLE mNotifyEvent{ nullptr };

    UINT32 mFrameStep{0u};
    std::atomic<UINT32> mPadding{0u};

    std::mutex mMutex;

    std::atomic<bool> mKillNow{true};
    std::thread mThread;
    std::promise<bool> mActivateCompletedPromise;

    DEF_NEWDEL(WasapiPlayback)
};


WasapiPlayback::~WasapiPlayback()
{
    close();

    if(mNotifyEvent != nullptr)
        CloseHandle(mNotifyEvent);
    mNotifyEvent = nullptr;
}


void WasapiPlayback::close()
{
    if (mRender)
        mRender->Release();
    mRender = nullptr;

    if (mClient)
        mClient->Release();
    mClient = nullptr;
}


FORCE_ALIGN int WasapiPlayback::mixerProc()
{
    SetRTPriority();
    althrd_setname(MIXER_THREAD_NAME);

    const ALuint update_size{mDevice->UpdateSize};
    const UINT32 buffer_len{mDevice->BufferSize};
    while(!mKillNow.load(std::memory_order_relaxed))
    {
        UINT32 written;
        HRESULT hr = mClient->GetCurrentPadding(&written);
        if(FAILED(hr))
        {
            ERR("Failed to get padding: 0x%08lx\n", hr);
            aluHandleDisconnect(mDevice, "Failed to retrieve buffer padding: 0x%08lx", hr);
            break;
        }
        mPadding.store(written, std::memory_order_relaxed);

        ALuint len{buffer_len - written};
        if(len < update_size)
        {
            DWORD res{WaitForSingleObjectEx(mNotifyEvent, 2000, FALSE)};
            if(res != WAIT_OBJECT_0)
                ERR("WaitForSingleObjectEx error: 0x%lx\n", res);
            continue;
        }

        BYTE *buffer;
        hr = mRender->GetBuffer(len, &buffer);
        if(SUCCEEDED(hr))
        {
            {
                std::lock_guard<std::mutex> _{mMutex};
                aluMixData(mDevice, buffer, len, mFrameStep);
                mPadding.store(written + len, std::memory_order_relaxed);
            }
            hr = mRender->ReleaseBuffer(len, 0);
        }
        if(FAILED(hr))
        {
            ERR("Failed to buffer data: 0x%08lx\n", hr);
            aluHandleDisconnect(mDevice, "Failed to send playback samples: 0x%08lx", hr);
            break;
        }
    }
    mPadding.store(0u, std::memory_order_release);

    return 0;
}


template <class T> void SafeRelease(__deref_inout_opt T **ppT)
{
    T *pTTemp = *ppT; // temp copy
    *ppT = nullptr;   // zero the input
    if (pTTemp)
    {
        pTTemp->Release();
    }
}

#ifndef SAFE_RELEASE
#define SAFE_RELEASE(x) { SafeRelease(&x); }
#endif


void WasapiPlayback::open(const ALCchar *name)
{
    // Get a string representing the Default Audio Device Renderer
    Platform::String^ deviceIdString = Windows::Media::Devices::MediaDevice::GetDefaultAudioRenderId(Windows::Media::Devices::AudioDeviceRole::Default);
    mDevId = deviceIdString->Begin();

    if (!name)
        name = "DefaultAudioRender";
    else if (strcmp(name, "DefaultAudioRender") != 0)
        throw al::backend_exception{ ALC_INVALID_VALUE, "Device name \"%s\" not found", name };

    mDevice->DeviceName = name;

    mNotifyEvent = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    if (mNotifyEvent == nullptr)
    {
        ERR("Failed to create notify events: %lu\n", GetLastError());
        throw al::backend_exception{ ALC_INVALID_VALUE, "Device init failed: 0x%08lx", E_FAIL };
    }
}


bool WasapiPlayback::reset()
{
    close();

    mActivateCompletedPromise.swap(decltype(mActivateCompletedPromise)()); // Reset promise

    IActivateAudioInterfaceAsyncOperation *asyncOp{ nullptr };
    HRESULT hr = ActivateAudioInterfaceAsync(mDevId.data(), __uuidof(IAudioClient), nullptr, this, &asyncOp);
    SAFE_RELEASE(asyncOp);
    if (FAILED(hr))
    {
        ERR("Failed to activate audio client: 0x%08lx\n", hr);
        return false;
    }

    // Wait ActivateCompleted to be finished
    auto activateCompletedFuture = mActivateCompletedPromise.get_future();
    activateCompletedFuture.wait();
    return activateCompletedFuture.get();
}

//
//  ActivateCompleted()
//
//  Callback implementation of ActivateAudioInterfaceAsync function.  This will be called on MTA thread
//  when results of the activation are available.
//
HRESULT WasapiPlayback::ActivateCompleted(IActivateAudioInterfaceAsyncOperation *operation)
{
    // Check for a successful activation result
    HRESULT hrActivateResult = S_OK;
    IUnknown *punkAudioInterface = nullptr;
    HRESULT hr = operation->GetActivateResult(&hrActivateResult, &punkAudioInterface);
    if (SUCCEEDED(hr) && SUCCEEDED(hrActivateResult))
    {
        // Get the pointer for the Audio Client
        punkAudioInterface->QueryInterface(IID_PPV_ARGS(&mClient));
        if (nullptr == mClient)
        {
            ERR("Failed to QueryInterface for mClient");
            mActivateCompletedPromise.set_value(false);
            return E_FAIL;
        }
    }
    SAFE_RELEASE(punkAudioInterface);
    punkAudioInterface = nullptr;

    WAVEFORMATEX *wfx;
    hr = mClient->GetMixFormat(&wfx);
    if(FAILED(hr))
    {
        ERR("Failed to get mix format: 0x%08lx\n", hr);
        mActivateCompletedPromise.set_value(false);
        return hr;
    }

    WAVEFORMATEXTENSIBLE OutputType;
    if(!MakeExtensible(&OutputType, wfx))
    {
        CoTaskMemFree(wfx);
        mActivateCompletedPromise.set_value(false);
        return E_FAIL;
    }
    CoTaskMemFree(wfx);
    wfx = nullptr;

    const ReferenceTime per_time{ReferenceTime{seconds{mDevice->UpdateSize}} / mDevice->Frequency};
    const ReferenceTime buf_time{ReferenceTime{seconds{mDevice->BufferSize}} / mDevice->Frequency};

    if(!mDevice->Flags.get<FrequencyRequest>())
        mDevice->Frequency = OutputType.Format.nSamplesPerSec;
    if(!mDevice->Flags.get<ChannelsRequest>())
    {
        const uint32_t chancount{OutputType.Format.nChannels};
        const DWORD chanmask{OutputType.dwChannelMask};
        if(chancount >= 8 && (chanmask&X71Mask) == X7DOT1)
            mDevice->FmtChans = DevFmtX71;
        else if(chancount >= 7 && (chanmask&X61Mask) == X6DOT1)
            mDevice->FmtChans = DevFmtX61;
        else if(chancount >= 6 && (chanmask&X51Mask) == X5DOT1)
            mDevice->FmtChans = DevFmtX51;
        else if(chancount >= 6 && (chanmask&X51RearMask) == X5DOT1REAR)
            mDevice->FmtChans = DevFmtX51Rear;
        else if(chancount >= 4 && (chanmask&QuadMask) == QUAD)
            mDevice->FmtChans = DevFmtQuad;
        else if(chancount >= 2 && (chanmask&StereoMask) == STEREO)
            mDevice->FmtChans = DevFmtStereo;
        else if(chancount >= 1 && (chanmask&MonoMask) == MONO)
            mDevice->FmtChans = DevFmtMono;
        else
            ERR("Unhandled channel config: %d -- 0x%08lx\n", chancount, chanmask);
    }

    OutputType.Format.wFormatTag = WAVE_FORMAT_EXTENSIBLE;
    switch(mDevice->FmtChans)
    {
    case DevFmtMono:
        OutputType.Format.nChannels = 1;
        OutputType.dwChannelMask = MONO;
        break;
    case DevFmtAmbi3D:
        mDevice->FmtChans = DevFmtStereo;
        /*fall-through*/
    case DevFmtStereo:
        OutputType.Format.nChannels = 2;
        OutputType.dwChannelMask = STEREO;
        break;
    case DevFmtQuad:
        OutputType.Format.nChannels = 4;
        OutputType.dwChannelMask = QUAD;
        break;
    case DevFmtX51:
        OutputType.Format.nChannels = 6;
        OutputType.dwChannelMask = X5DOT1;
        break;
    case DevFmtX51Rear:
        OutputType.Format.nChannels = 6;
        OutputType.dwChannelMask = X5DOT1REAR;
        break;
    case DevFmtX61:
        OutputType.Format.nChannels = 7;
        OutputType.dwChannelMask = X6DOT1;
        break;
    case DevFmtX71:
        OutputType.Format.nChannels = 8;
        OutputType.dwChannelMask = X7DOT1;
        break;
    }
    switch(mDevice->FmtType)
    {
    case DevFmtByte:
        mDevice->FmtType = DevFmtUByte;
        /* fall-through */
    case DevFmtUByte:
        OutputType.Format.wBitsPerSample = 8;
        OutputType.Samples.wValidBitsPerSample = 8;
        OutputType.SubFormat = KSDATAFORMAT_SUBTYPE_PCM;
        break;
    case DevFmtUShort:
        mDevice->FmtType = DevFmtShort;
        /* fall-through */
    case DevFmtShort:
        OutputType.Format.wBitsPerSample = 16;
        OutputType.Samples.wValidBitsPerSample = 16;
        OutputType.SubFormat = KSDATAFORMAT_SUBTYPE_PCM;
        break;
    case DevFmtUInt:
        mDevice->FmtType = DevFmtInt;
        /* fall-through */
    case DevFmtInt:
        OutputType.Format.wBitsPerSample = 32;
        OutputType.Samples.wValidBitsPerSample = 32;
        OutputType.SubFormat = KSDATAFORMAT_SUBTYPE_PCM;
        break;
    case DevFmtFloat:
        OutputType.Format.wBitsPerSample = 32;
        OutputType.Samples.wValidBitsPerSample = 32;
        OutputType.SubFormat = KSDATAFORMAT_SUBTYPE_IEEE_FLOAT;
        break;
    }
    OutputType.Format.nSamplesPerSec = mDevice->Frequency;

    OutputType.Format.nBlockAlign = static_cast<WORD>(OutputType.Format.nChannels *
        OutputType.Format.wBitsPerSample / 8);
    OutputType.Format.nAvgBytesPerSec = OutputType.Format.nSamplesPerSec *
        OutputType.Format.nBlockAlign;

    TraceFormat("Requesting playback format", &OutputType.Format);
    hr = mClient->IsFormatSupported(AUDCLNT_SHAREMODE_SHARED, &OutputType.Format, &wfx);
    if(FAILED(hr))
    {
        ERR("Failed to check format support: 0x%08lx\n", hr);
        hr = mClient->GetMixFormat(&wfx);
    }
    if(FAILED(hr))
    {
        ERR("Failed to find a supported format: 0x%08lx\n", hr);
        mActivateCompletedPromise.set_value(false);
        return hr;
    }

    if(wfx != nullptr)
    {
        TraceFormat("Got playback format", wfx);
        if(!MakeExtensible(&OutputType, wfx))
        {
            CoTaskMemFree(wfx);
            mActivateCompletedPromise.set_value(false);
            return E_FAIL;
        }
        CoTaskMemFree(wfx);
        wfx = nullptr;

        mDevice->Frequency = OutputType.Format.nSamplesPerSec;
        const uint32_t chancount{OutputType.Format.nChannels};
        const DWORD chanmask{OutputType.dwChannelMask};
        if(chancount >= 8 && (chanmask&X71Mask) == X7DOT1)
            mDevice->FmtChans = DevFmtX71;
        else if(chancount >= 7 && (chanmask&X61Mask) == X6DOT1)
            mDevice->FmtChans = DevFmtX61;
        else if(chancount >= 6 && (chanmask&X51Mask) == X5DOT1)
            mDevice->FmtChans = DevFmtX51;
        else if(chancount >= 6 && (chanmask&X51RearMask) == X5DOT1REAR)
            mDevice->FmtChans = DevFmtX51Rear;
        else if(chancount >= 4 && (chanmask&QuadMask) == QUAD)
            mDevice->FmtChans = DevFmtQuad;
        else if(chancount >= 2 && (chanmask&StereoMask) == STEREO)
            mDevice->FmtChans = DevFmtStereo;
        else if(chancount >= 1 && (chanmask&MonoMask) == MONO)
            mDevice->FmtChans = DevFmtMono;
        else
        {
            ERR("Unhandled extensible channels: %d -- 0x%08lx\n", OutputType.Format.nChannels,
                OutputType.dwChannelMask);
            mDevice->FmtChans = DevFmtStereo;
            OutputType.Format.nChannels = 2;
            OutputType.dwChannelMask = STEREO;
        }

        if(IsEqualGUID(OutputType.SubFormat, KSDATAFORMAT_SUBTYPE_PCM))
        {
            if(OutputType.Format.wBitsPerSample == 8)
                mDevice->FmtType = DevFmtUByte;
            else if(OutputType.Format.wBitsPerSample == 16)
                mDevice->FmtType = DevFmtShort;
            else if(OutputType.Format.wBitsPerSample == 32)
                mDevice->FmtType = DevFmtInt;
            else
            {
                mDevice->FmtType = DevFmtShort;
                OutputType.Format.wBitsPerSample = 16;
            }
        }
        else if(IsEqualGUID(OutputType.SubFormat, KSDATAFORMAT_SUBTYPE_IEEE_FLOAT))
        {
            mDevice->FmtType = DevFmtFloat;
            OutputType.Format.wBitsPerSample = 32;
        }
        else
        {
            ERR("Unhandled format sub-type: %s\n", GuidPrinter{OutputType.SubFormat}.c_str());
            mDevice->FmtType = DevFmtShort;
            if(OutputType.Format.wFormatTag != WAVE_FORMAT_EXTENSIBLE)
                OutputType.Format.wFormatTag = WAVE_FORMAT_PCM;
            OutputType.Format.wBitsPerSample = 16;
            OutputType.SubFormat = KSDATAFORMAT_SUBTYPE_PCM;
        }
        OutputType.Samples.wValidBitsPerSample = OutputType.Format.wBitsPerSample;
    }
    mFrameStep = OutputType.Format.nChannels;

//    EndpointFormFactor formfactor{UnknownFormFactor};
//    get_device_formfactor(mMMDev, &formfactor);
//    mDevice->IsHeadphones = (mDevice->FmtChans == DevFmtStereo
//        && (formfactor == Headphones || formfactor == Headset));

    setChannelOrderFromWFXMask(OutputType.dwChannelMask);

    hr = mClient->Initialize(AUDCLNT_SHAREMODE_SHARED, AUDCLNT_STREAMFLAGS_EVENTCALLBACK,
        buf_time.count(), 0, &OutputType.Format, nullptr);
    if(FAILED(hr))
    {
        ERR("Failed to initialize audio client: 0x%08lx\n", hr);
        mActivateCompletedPromise.set_value(false);
        return hr;
    }

    UINT32 buffer_len{};
    ReferenceTime min_per{};
    hr = mClient->GetDevicePeriod(&reinterpret_cast<REFERENCE_TIME&>(min_per), nullptr);
    if(SUCCEEDED(hr))
        hr = mClient->GetBufferSize(&buffer_len);
    if(FAILED(hr))
    {
        ERR("Failed to get audio buffer info: 0x%08lx\n", hr);
        mActivateCompletedPromise.set_value(false);
        return hr;
    }

    /* Find the nearest multiple of the period size to the update size */
    if(min_per < per_time)
        min_per *= maxi64((per_time + min_per/2) / min_per, 1);
    mDevice->UpdateSize = minu(RefTime2Samples(min_per, mDevice->Frequency), buffer_len/2);
    mDevice->BufferSize = buffer_len;

    hr = mClient->SetEventHandle(mNotifyEvent);
    if(FAILED(hr))
    {
        ERR("Failed to set event handle: 0x%08lx\n", hr);
        mActivateCompletedPromise.set_value(false);
        return hr;
    }

    mActivateCompletedPromise.set_value(true);
    return hr;
    // Need to return S_OK
    //return S_OK;
}


void WasapiPlayback::start()
{
    ResetEvent(mNotifyEvent);

    // Start ///////////
    HRESULT hr = mClient->Start();
    if (FAILED(hr))
    {
        ERR("Failed to start audio client: 0x%08lx\n", hr);
        return;
    }

    // Get the render client
    hr = mClient->GetService(__uuidof(IAudioRenderClient), (void**)&mRender);
    if (FAILED(hr))
    {
        ERR("Failed to get IAudioRenderClient: 0x%08lx\n", hr);
        return;
    }

    try {
        mKillNow.store(false, std::memory_order_release);
        mThread = std::thread{ std::mem_fn(&WasapiPlayback::mixerProc), this };
    }
    catch (...) {
        ERR("Failed to start thread\n");
        mClient->Stop();
    }
}


void WasapiPlayback::stop()
{
    if(!mRender || !mThread.joinable())
        return;

    mKillNow.store(true, std::memory_order_release);
    mThread.join();

    mClient->Stop();
}


ClockLatency WasapiPlayback::getClockLatency()
{
    ClockLatency ret;

    std::lock_guard<std::mutex> _{mMutex};
    ret.ClockTime = GetDeviceClockTime(mDevice);
    ret.Latency  = std::chrono::seconds{mPadding.load(std::memory_order_relaxed)};
    ret.Latency /= mDevice->Frequency;

    return ret;
}


} // namespace


bool WasapiUwpBackendFactory::init()
{
    return true;
}

bool WasapiUwpBackendFactory::querySupport(BackendType type)
{ 
    return type == BackendType::Playback;
}

std::string WasapiUwpBackendFactory::probe(BackendType type)
{
    std::string outnames;
    switch(type)
    {
    case BackendType::Playback:
        outnames.append("DefaultAudioRender");
        break;

    case BackendType::Capture:
        break;
    }

    return outnames;
}

BackendPtr WasapiUwpBackendFactory::createBackend(ALCdevice *device, BackendType type)
{
    if(type == BackendType::Playback)
        return BackendPtr{new WasapiPlayback{device}};
return nullptr;
}

BackendFactory &WasapiUwpBackendFactory::getFactory()
{
    static WasapiUwpBackendFactory factory{};
    return factory;
}
