
# AWS IoT Device SDK C


## Branches


### master branch
The [master](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master) branch hosts the continuous development of the AWS IoT Embedded C SDK libraries. Please be aware that the libraries in master branch may have bugs and performance issues. Consider using the released versions of the AWS IoT Embedded C SDK for production ready software.

### v4_beta_deprecated branch (Formerly named v4_beta)
The [v4_beta_deprecated](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta_deprecated) branch contains a beta version of the AWS IoT Embedded C SDK libraries, which is now deprecated. This branch was earlier named as *v4_beta*, and was renamed to *v4_beta_deprecated*. The libraries in this branch will not be released. However, critical bugs will be fixed and tested. No new features will be added to this branch.


## Releases

All of the released versions of the AWS IoT Embedded C SDK libraries are available as git tags. For example, the last release of the v3 SDK version is available at [tag 3.0.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v3.0.1).

## Building and Running Demos

  

The libraries in this SDK are not dependent on any operating systems. However, the demos for the libraries in this SDK are built and tested on a Linux platform. This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool.



### Prerequisites

- CMake 3.13.0 or later and a C90 compiler.

- A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems.
    - Linux system with POSIX sockets and timer APIs. (CI tests on Ubuntu 18.04).
        - On Linux systems, installation of OpenSSL development libraries and header files, *version 1.1.0 or later*, are required. The OpenSSL development libraries are usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.
        - Although not a part of the C90 standard, `stdint.h` is required for fixed-width integer types (e.g int32_t).



### AWS IoT Account Setup

It is required to setup an AWS account and access the AWS IoT Console for running demos and tests. Follow the links to:

-  [Setup an AWS account](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html).

-  [Sign-in to the AWS IoT Console](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html) after setting up the AWS account.



*Note: If using the Provisioning library, a fleet provisioning template, a provisioning claim, IoT policies and IAM policies need to be setup for the AWS account. Complete the steps to setup your device and AWS IoT account outlined [here](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#use-claim).*



### Configuring the mutual auth demos

- You can pass the following configuration settings as command line options in order to run the mutual auth demos: 
```bash
cmake .. -DAWS_IOT_ENDPOINT="aws-iot-endpoint" -DROOT_CA_CERT_PATH="root-ca-path" -DCLIENT_CERT_PATH="certificate-path" -DCLIENT_PRIVATE_KEY_PATH="private-key-path" 
```

- In order to set these configurations manually, edit `demo_config.h` in `demos/mqtt/mqtt_demo_mutual_auth/` and `demos/http/http_demo_mutual_auth/` to `#define` the following:

	- Set `AWS_IOT_ENDPOINT` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`.

	- Set `ROOT_CA_CERT_PATH` to the path of the root CA certificate downloaded when setting up the device certificate (or Provisioning Claim for Fleet Provisioning) in [AWS IoT Account Setup](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta#aws-iot-account-setup).

	- Set `CLIENT_CERT_PATH` to the path of the client certificate downloaded when setting up the device certificate (or Provisioning Claim for Fleet Provisioning) in [AWS IoT Account Setup](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta#aws-iot-account-setup).

	- Set `CLIENT_PRIVATE_KEY_PATH` to the path of the private key downloaded when setting up the device certificate (or Provisioning Claim for Fleet Provisioning) in [AWS IoT Account Setup](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta#aws-iot-account-setup).



### Build Steps

1. Go to the root directory of this repository.

1. Create build directory: `mkdir build && cd build`

1. Run *cmake* while inside build directory: `cmake ..`

1. Run this command to build the demos: `make`

1. Go to the `build/bin` directory and run any demo executables from there.

### Alternative option of Docker containers for running demos locally.

Install Docker:

```shell

curl -fsSL https://get.docker.com -o get-docker.sh

sh get-docker.sh

```

#### Installing Mosquitto to run MQTT demos locally

The following instructions have been tested on an Ubuntu 18.04 environment with Docker and OpenSSL installed.

1.  Download the official Docker image for Mosquitto.

```shell

docker pull eclipse-mosquitto:latest

```
2.  `BROKER_ENDPOINT` defined in `demos/mqtt/mqtt_demo_basic_tls/demo_config.h` can now be set to `localhost`.

3. For TLS communication with Mosquitto broker, server and CA credentials need to be created. Use OpenSSL commands to generate the credentials for the Mosquitto server.
```shell
# Generate CA key and certificate. Provide the Subject field information as appropriate.
openssl req -x509 -nodes -sha256 -days 365 -newkey rsa:2048 -keyout ca.key -out ca.crt
```

```shell
# Generate server key and certificate.
openssl req -nodes -sha256 -new -keyout server.key -out server.csr
# Sign with the CA cert.
openssl x509 -req -sha256 -in server.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out server.crt -days 365

```

4. Create a mosquitto.conf file to use port 8883 (for TLS communication) and providing path to the generated credentials.

```
port 8883

cafile /mosquitto/config/ca.crt
certfile /mosquitto/config/server.crt
keyfile /mosquitto/config/server.key

# Use this option for TLS mutual authentication (where client will provide CA signed certificate)
#require_certificate true
tls_version tlsv1.2
#use_identity_as_username true

```

5. Run the docker container from the local directory containing the generated credential and mosquitto.conf files.

```shell
docker run -it -p 8883:8883 -v $(pwd):/mosquitto/config/ --name mosquitto-basic-tls eclipse-mosquitto:latest
```

6. Set `ROOT_CA_CERT_PATH` to the absolute path of the CA certificate created in step 3. for the local Mosquitto server.

## Generating Documentation

The Doxygen references were created using Doxygen version 1.8.20. To generate the
Doxygen pages, use the provided Python script, [tools/doxygen/generate_docs.py](tools/doxygen/generate_docs.py).
Please ensure that each of the library submodules under **libraries/standard/** and **libraries/aws** are cloned before using
this script.

```shell
cd <CSDK_ROOT>
python3 docs/doxygen/generate_docs.py --root .
```

The generated documentation landing page is located at **docs/doxygen/output/html/index.html**.
