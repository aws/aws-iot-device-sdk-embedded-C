
# AWS IoT Device SDK for Embedded C


**[API documentation](https://docs.aws.amazon.com/freertos/latest/lib-ref/embedded-csdk/202009.00/lib-ref/index.html)**    

We have released version 202009.00 of the AWS IoT Device SDK for Embedded-C (C-SDK). This release includes refactored MQTT, JSON Parser, and AWS IoT Device Shadow libraries for optimized memory usage and modularity, and includes dependent libraries via GitHub submoduling. These libraries have gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score over 8, and checks against deviations from mandatory rules in the [MISRA coding standard](https://www.misra.org.uk/MISRAHome/MISRAC2012/tabid/196/Default.aspx). Deviations from the MISRA C:2012 guidelines are documented under [MISRA Deviations](MISRA.md). This library has also undergone both static code analysis from [Coverity static analysis](https://scan.coverity.com/), and validation of memory safety and proof of functional correctness through the CBMC automated reasoning tool.  

If you are upgrading from v3.x of the C-SDK to the 202009.00 release, please follow the [migration guide](https://docs.aws.amazon.com/freertos/latest/lib-ref/embedded-csdk/202009.00/lib-ref/docs/doxygen/output/html/migration_guide.html). If you are using the C-SDK v4_beta_deprecated branch, note that we will continue to maintain this branch for critical bug fixes and security patches but will not add new features to it. See the C-SDK v4_beta_deprecated branch [README](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/v4_beta_deprecated/README.md) for additional details. 

## Overview

The AWS IoT Device SDK for Embedded C (C-SDK) is a collection of C source files under the [MIT open source license](LICENSE) that can be used in embedded applications to securely connect IoT devices to [AWS IoT Core](http://docs.aws.amazon.com/iot/latest/developerguide/what-is-aws-iot.html). It includes a MQTT, JSON Parser, and AWS IoT Device Shadow library. It is distributed in source form and intended to be built into customer firmware along with application code, other libraries and RTOS. 

## Features

The C-SDK simplifies access to the Pub/Sub functionality of the AWS IoT broker via MQTT and provides APIs to interact with Device Shadow. The SDK has been tested to work with the AWS IoT Core and an open source MQTT broker to ensure best interoperability of a device with the AWS IoT platform. The C-SDK contains the following libraries:

### MQTT 
The C-SDK provides the ability to establish an MQTT connection with a broker over a customer-implemented transport layer, which can either be a secure channel like a TLS session (mutually authenticated or server-only authentication) or a non-secure channel like a plaintext TCP connection. This MQTT connection can be used for performing publish operations to MQTT topics and subscribing to MQTT topics. The SDK provides a mechanism to register customer-defined callbacks for receiving incoming PUBLISH, acknowledgement and keep-alive response events from the broker.  The [coreMQTT](https://github.com/FreeRTOS/coreMQTT) library has been refactored for memory optimization and is fully compliant with the [MQTT 3.1.1](http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/mqtt-v3.1.1.html) standard.  It has no dependencies on any additional libraries other than the standard C library, a customer-implemented network transport interface, and *optionally* a customer-implemented platform time function.  The refactored design embraces different use-cases, ranging from resource-constrained platforms using only QoS 0 MQTT PUBLISH messages to resource-rich platforms using QoS 2 MQTT PUBLISH over TLS connections.  

### AWS IoT Device Shadow
[AWS IoT Device Shadow](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk) enables you to store and retrieve the current state (the “shadow”) of every registered device. The device’s shadow is a persistent, virtual representation of your device that you can interact with from AWS IoT Core even if the device is offline. The device state captured as its “shadow” is itself a [JSON](https://www.json.org/) document. The device can send commands over MQTT or HTTP to update its latest state. Each device’s shadow is uniquely identified by the name of the corresponding “thing”, a representation of a specific device or logical entity on the AWS Cloud. See [Managing Devices with AWS IoT](https://docs.aws.amazon.com/iot/latest/developerguide/iot-thing-management.html) for more information. More details about shadows can be found in [AWS IoT documentation](https://docs.aws.amazon.com/iot/latest/developerguide/iot-device-shadows.html). 

### JSON Parser
The coreJSON library is a JSON parser that strictly enforces the [ECMA-404 JSON standard](https://www.json.org/json-en.html).

## Metrics

Within the MQTT Demo, users have the ability to report operating System, hardware platform and MQTT Client information to AWS IoT by sending a specially formatted string in the username field of the MQTT CONNECT packet.  

### Format

The format of the username string with metrics is:
```
<Actual_Username>?SDK=<OS_Name>&Version=<OS_Version>&Platform=<Hardware_Platform>&MQTTLib=<MQTT_Library_name>@<MQTT_Library_version>
```
where

* **Actual_Username** is the actual username used for authentication (if a username/password is used for authentication).
* **OS_Name** is the Operating System the application is running on.
* **OS_Version** is the version number of the Operating System.
* **Hardware_Platform** is the Hardware Platform the application is running on.
* **MQTT_Library_name** is the MQTT Client library being used.
* **MQTT_Library_version** is the version of the MQTT Client library being used.



## Branches

### master branch
The [master](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master) branch hosts the continuous development of the AWS IoT Embedded C SDK libraries. Please be aware that the development at the tip of the master branch is continuously in progress and may have bugs. Consider using the tagged releases of the AWS IoT Embedded C SDK for production ready software.

### v4_beta_deprecated branch (Formerly named v4_beta)
The [v4_beta_deprecated](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta_deprecated) branch contains a beta version of the AWS IoT Embedded C SDK libraries, which is now deprecated. This branch was earlier named as *v4_beta*, and was renamed to *v4_beta_deprecated*. The libraries in this branch will not be released. However, critical bugs will be fixed and tested. No new features will be added to this branch.


## Releases

All of the released versions of the AWS IoT Embedded C SDK libraries are available as git tags. For example, the last release of the v3 SDK version is available at [tag 3.0.1](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v3.0.1).

## Versioning

C-SDK releases will now follow a date based versioning scheme with the format YYYYMM.NN_major, where: 

* Y represents the year.
* M represents the month.
* N represents the release order within the designated month (00 being the first release).
* A "major" denotation indicates the addition of new features or significant updates to multiple libraries. 

For example, a second release in June 2021 would be 202106.01. Although the SDK releases have moved to date-based versioning, each library within the SDK will still retain semantic versioning. In semantic versioning, the version number itself (X.Y.Z) indicates whether the release is a major, minor, or point release. You can use the semantic version of a library to assess the scope and impact of a new release on your application. 

## Cloning
This repo uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules (The ZIP file is also not a valid git repository).  If you download from the [202009.00 Release Page](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/202009.00) page, you will get the entire repository (including the submodules) in the ZIP file, aws-iot-device-sdk-embedded-c-202009.00.zip.  


To clone using HTTPS:
```
git clone https://github.com/aws/aws-iot-device-sdk-embedded-C.git --recurse-submodules
```
Using SSH:
```
git clone git@github.com:aws/aws-iot-device-sdk-embedded-C.git --recurse-submodules
```

If you have downloaded the repo without using the `--recurse-submodules` argument, you need to run:
```
git submodule update --init --recursive
```


## Building and Running Demos

  
The libraries in this SDK are not dependent on any operating system. However, the demos for the libraries in this SDK are built and tested on a Linux platform. This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool.


### Prerequisites

- CMake 3.13.0 or later 

- C90 compiler

- Although not a part of the C90 standard, `stdint.h` is required for fixed-width integer types (e.g int32_t).

- A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems.
    - Linux system with POSIX sockets and timer APIs. (CI tests on Ubuntu 18.04).
        - On Linux systems, installation of OpenSSL development libraries and header files, *version 1.1.0 or later*, are required. The OpenSSL development libraries are usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.
        



### AWS IoT Account Setup

It is required to setup an AWS account and access the AWS IoT Console for running demos and tests. Follow the links to:

-  [Setup an AWS account](https://portal.aws.amazon.com/billing/signup#/start).

-  [Sign-in to the AWS IoT Console](https://aws.amazon.com/console/) after setting up the AWS account.



### Configuring the MQTT mutual auth demo

- You can pass the following configuration settings as command line options in order to run the mutual auth demo:
```bash
cmake .. -DAWS_IOT_ENDPOINT="aws-iot-endpoint" -DROOT_CA_CERT_PATH="root-ca-path" -DCLIENT_CERT_PATH="certificate-path" -DCLIENT_PRIVATE_KEY_PATH="private-key-path" 
```

- In order to set these configurations manually, edit `demo_config.h` in `demos/mqtt/mqtt_demo_mutual_auth/` to `#define` the following:

	- Set `AWS_IOT_ENDPOINT` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`.

	- Set `ROOT_CA_CERT_PATH` to the path of the root CA certificate downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).

	- Set `CLIENT_CERT_PATH` to the path of the client certificate downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).

	- Set `CLIENT_PRIVATE_KEY_PATH` to the path of the private key downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).


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
python3 tools/doxygen/generate_docs.py --root .
```

The generated documentation landing page is located at **docs/doxygen/output/html/index.html**

## License

The C-SDK libraries are licensed under the [MIT License](LICENSE).
