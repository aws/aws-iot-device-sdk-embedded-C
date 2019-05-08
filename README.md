# AWS IoT Device SDK C v4.0.0 Beta

**[Link to API documentation](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/index.html)**

[![Build Status](https://travis-ci.org/aws/aws-iot-device-sdk-embedded-C.svg?branch=v4_beta)](https://travis-ci.org/aws/aws-iot-device-sdk-embedded-C)
[![Coverage Status](https://coveralls.io/repos/github/aws/aws-iot-device-sdk-embedded-C/badge.svg?branch=v4_beta)](https://coveralls.io/github/aws/aws-iot-device-sdk-embedded-C?branch=v4_beta)

The AWS IoT Device SDK for C is a collection of C99 source files that allow applications to securely connect to the AWS IoT platform. It includes an MQTT 3.1.1 client, as well as libraries specific to AWS IoT, such as Thing Shadows. It is distributed in source form and may be built into firmware along with application code.

This library, currently a Beta release, will supersede both the AWS IoT Device SDK Embedded C and the libraries provided with Amazon FreeRTOS.

## Beta Features

This Beta library is a new design that inherits from both the AWS IoT Device SDK Embedded C and the libraries provided with Amazon FreeRTOS. In addition, it provides the following new features:
- Asynchronous API for both MQTT and Thing Shadow.
- Multithreaded API by default (removed the `yield` function).
- More efficient platform layer (especially timers).
- Complete separation of MQTT and network stack, allowing MQTT to run over any network stack.
- Configurable memory allocation (static-only or dynamic). Memory allocation functions may also be set by the user.
- Network stack based on OpenSSL.
- MQTT persistent session support.

Compared to the AWS IoT Device SDK Embedded C v3.0.1, the following features are missing:
- Auto-reconnect for MQTT connections.
- Shadow JSON document generator.
- Jobs API.
- Build support for Apple macOS.

## Building and Running Demos

**Main documentation page:** [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/building.html)

This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool. **As of now, this Beta release only builds on Linux.**

### Prerequisites
- Linux system with support for POSIX threads and timers.
- CMake 3.5.0 or later.

If using the OpenSSL network implementation:
- OpenSSL development libraries and header files, version 1.0.2g or later. This is usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.

### Build Steps
1. Clone the source code and submodules. This SDK uses third-party libraries as submodules in the `third_party` directory.
    - If the source code is downloaded via `git clone`, nothing further needs to be done. The CMake build system can automatically clone submodules in this case.
    - For any other download, the submodules must be downloaded and placed in their respective `third_party` directory.
        - [mbed TLS](https://github.com/ARMmbed/mbedtls/tree/mbedtls-2.17) → `third_party/mbedtls/mbedtls`
        - [tinyCBOR](https://github.com/intel/tinycbor) → `third_party/tinycbor/tinycbor`
2. Complete the first 6 steps in the guide [Getting Started with AWS IoT](https://docs.aws.amazon.com/iot/latest/developerguide/iot-gs.html). The guide mentions the AWS IoT Button, but you do not need one to use this SDK.
    1. [Sign in to the AWS IoT Console](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html)
    2. [Register a Device in the Registry](https://docs.aws.amazon.com/iot/latest/developerguide/register-device.html)
    3. [Create and Activate a Device Certificate](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html)
    4. [Create an AWS IoT Policy](https://docs.aws.amazon.com/iot/latest/developerguide/create-iot-policy.html)
    5. [Attach an AWS IoT Policy to a Device Certificate](https://docs.aws.amazon.com/iot/latest/developerguide/attach-policy-to-certificate.html)
    6. [Attach a Certificate to a Thing](https://docs.aws.amazon.com/iot/latest/developerguide/attach-cert-thing.html)
3. *Optional:* Set the following `#define` in [iot_config.h](demos/iot_config.h). You may skip this step and instead pass these configuration settings as command line options when running the demos.
    - Set `IOT_DEMO_IDENTIFIER` to the Thing Name you set in [step 1.2](https://docs.aws.amazon.com/iot/latest/developerguide/register-device.html). The corresponding command line option for this constant is `-i`.
    - Set `IOT_DEMO_SERVER` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`. The corresponding command line option for this constant is `-h`.
    - Set `IOT_DEMO_ROOT_CA` to the path of the root CA certificate downloaded in [step 1.3](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html). The corresponding command line option for this constant is `-r`.
    - Set `IOT_DEMO_CLIENT_CERT` to the path of the client certificate downloaded in [step 1.3](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html). The corresponding command line option for this constant is `-c`.
    - Set `IOT_DEMO_PRIVATE_KEY` to the path of the private downloaded in [step 1.3](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html). The corresponding command line option for this constant is `-k`.
4. Make a build directory in the SDK's root directory and `cd` into it.
    ```sh
    mkdir build
    cd build
    ```
5. Run CMake, then `make`. This builds the demo executables and places them in `build/bin`.
    ```sh
    cmake ..
    make
    ```

See the documentation page [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/building.html) for a list of options that can be used to configure the build system.

## Porting the SDK

Please refer to the [Porting Guide](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/guide_developer_porting.html) for instructions on porting this SDK.

## License

This library is licensed under the [MIT License](LICENSE).
