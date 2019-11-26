# AWS IoT Device SDK C with Fleet Provisioning<sup>BETA</sup> support

**[Link to API documentation](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/index.html)**

[![Build Status](https://travis-ci.org/aws/aws-iot-device-sdk-embedded-C.svg?branch=FleetProvisioning_beta)](https://travis-ci.org/aws/aws-iot-device-sdk-embedded-C)
[![Coverage Status](https://coveralls.io/repos/github/aws/aws-iot-device-sdk-embedded-C/badge.svg?branch=FleetProvisioning_beta)](https://coveralls.io/github/aws/aws-iot-device-sdk-embedded-C?branch=FleetProvisioning_beta)

The AWS IoT Device SDK for C is a collection of C99 source files that allow applications to securely connect to the AWS IoT platform. It includes an MQTT 3.1.1 client, as well as libraries specific to AWS IoT, such as Thing Shadows. It is distributed in source form and may be built into firmware along with application code.

This library supersedes both the AWS IoT Device SDK Embedded C and the libraries provided with Amazon FreeRTOS.

## Features

This branch contains all libraries from the [v4_beta](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta) branch, and <b>an additional library to facilitate use of AWS Iot Core's Fleet Provisioning<sup>BETA</sup> feature</b>. The Fleet Provisioning feature can be used to automatically set up generically manufactured devices with unique digital identities, IoT Policies, and other required device-side and cloud-side configurations upon devices’ first connection to AWS IoT Core. For more information, refer to [Provisioning Devices That Don't Have Device Certificates Using Fleet Provisioning](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html).

## Building and Running the Fleet Provisioning library Demo

**Main documentation page:** [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/building.html)

This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool. This repo contains a ready-to-use port for Linux.

### Prerequisites
- CMake 3.5.0 or later and a C99 compiler.
- A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems. For reference, the version used by this repo's Travis CI builds are listed in parentheses.
    - Linux system with POSIX thread and timer APIs. (CI tests on Ubuntu 16.04).<br>
    On Linux systems, the OpenSSL network implementation may be used instead of the default network implementation based on mbed TLS. This requires the installation of OpenSSL development libraries and header files, version 1.0.2g or later. The OpenSSL development libraries are usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.

### Build Steps
1. Clone the source code and submodules. This SDK uses third-party libraries as submodules in the `third_party` directory.
    - If the source code is downloaded via `git clone`, nothing further needs to be done. The CMake build system can automatically clone submodules in this case.
    - For any other download, the submodules must be downloaded and placed in their respective `third_party` directory.
        - [mbed TLS](https://github.com/ARMmbed/mbedtls/tree/mbedtls-2.17) → `third_party/mbedtls/mbedtls`
        - [tinyCBOR](https://github.com/intel/tinycbor) → `third_party/tinycbor/tinycbor`
2. For running the demo with the fleet provisioning feature, a fleet provisioning template, a provisioning claim, IoT policies and IAM policies will need to be setup on an AWS IoT account. ([Instructions for setting up an AWS IoT account](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html)). Complete the steps to setup your device and AWS IoT account outlined [here](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#use-claim).
3. *Required:* Set the following `#define` in [iot_config.h](demos/iot_config.h). The demo requires configuration with 2 parameter name-value pairs for sending to the AWS IoT Core service. These parameters should be supported by the created fleet provisioning template. Update the created fleet provisioning template to accept an extra parameter (besides Certificate ID and Serial Number that are created by default), refer to the [Parameters section](https://docs.aws.amazon.com/iot/latest/developerguide/provision-template.html#parameters-section) of [Fleet Provisioning Template](https://docs.aws.amazon.com/iot/latest/developerguide/provision-template.html#fleet-provision-template).
    - Set `AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME` with the name of the fleet provisioning template created in step 1. of [Provisioning by claim](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#use-claim).
    - Set `AWS_IOT_DEMO_PROVISIONING_PARAMETER_NAME_SERIAL_NUMBER_VALUE` with the value of the device's serial number (or an equivalent unique device identifier) that will be used to create a Thing resource by the fleet provisioning template.
    - Set `AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME` with the name of an additional parameter that the device needs to send to the fleet provisioning template. The demo requires exactly 2 different parameter name-value pairs (including serial number) to be configured. 
    - Set `AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE` with the value of the additional parameter.
4. *Optional:* Set the following `#define` in [iot_config.h](demos/iot_config.h). You may skip this step and instead pass these configuration settings as command line options when running the demos.
    - Set `IOT_DEMO_IDENTIFIER` to a MQTT client identifier that you want to use for the MQTT connection to AWS IoT Core. The corresponding command line option for this constant is `-i`.
    - Set `IOT_DEMO_SERVER` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`. The corresponding command line option for this constant is `-h`.
    - Set `IOT_DEMO_ROOT_CA` to the path of the root CA certificate downloaded during the setup of provisioning claim in step 2 of [Build Steps](https://github.com/aws/aws-iot-device-sdk-embedded-C-staging/tree/fleetprovisioning_beta#build-steps). The corresponding command line option for this constant is `-r`.
    - Set `IOT_DEMO_CLIENT_CERT` to the path of the client certificate downloaded during the setup of provisioning claim in step 2 of [Build Steps](https://github.com/aws/aws-iot-device-sdk-embedded-C-staging/tree/fleetprovisioning_beta#build-steps). The corresponding command line option for this constant is `-c`.
    - Set `IOT_DEMO_PRIVATE_KEY` to the path of the private downloaded during the setup of provisioning claim in step 2 of [Build Steps](https://github.com/aws/aws-iot-device-sdk-embedded-C-staging/tree/fleetprovisioning_beta#build-steps). The corresponding command line option for this constant is `-k`.
    - Set `IOT_DEMO_USER_NAME` to the username string, if any, required to authenticate to your MQTT broker. The corresponding command line option for this constant is `-m`.
    - Set `IOT_DEMO_PASSWORD` to the password string, if any, required to authenticate to your MQTT broker. The corresponding command line option for this constant is `-w`.
5. Make a build directory in the SDK's root directory and `cd` into it.
    ```sh
    mkdir build
    cd build
    ```
6. Run CMake from the build directory.
    ```sh
    cmake ..
    ```
    CMake will generate a project based on the detected operating system. On Linux, the default project is a Makefile. To build the SDK with this Makefile, run `make`. The resulting binaries (the demo executables) and libraries will be placed in the `build/output` directory.

    You may also use CMake GUI. Specify the SDK's root directory as the source directory and the build directory created in step 5 as the build directory in CMake GUI.

See the documentation page [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/building.html) for a list of options that can be used to configure the build system.

## Porting the SDK

Please refer to the [Porting Guide](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/guide_developer_porting.html) for instructions on porting this SDK.

Existing ports (which may be used as examples) are present in `ports`. A blank template for implementing new ports is in `ports/template`.

## License

This library is licensed under the [MIT License](LICENSE).
