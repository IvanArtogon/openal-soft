#ifndef BACKENDS_WASAPI_UWP_H
#define BACKENDS_WASAPI_UWP_H

#include "backends/base.h"

struct WasapiUwpBackendFactory final : public BackendFactory {
public:
    bool init() override;

    bool querySupport(BackendType type) override;

    std::string probe(BackendType type) override;

    BackendPtr createBackend(ALCdevice *device, BackendType type) override;

    static BackendFactory &getFactory();
};

#endif /* BACKENDS_WASAPI_UWP_H */