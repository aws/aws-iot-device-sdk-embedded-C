
# AWS IoT Device SDK for Embedded C

## Table of Contents

* [Overview](#overview)
    * [License](#license)
    * [Features](#features)
        * [coreMQTT](#coremqtt)
        * [coreHTTP](#corehttp)
        * [coreJSON](#corejson)
        * [corePKCS11](#corepkcs11)
        * [AWS IoT Device Shadow](#aws-iot-device-shadow)
        * [AWS IoT Jobs](#aws-iot-jobs)
        * [AWS IoT Device Defender](#aws-iot-device-defender)
        * [AWS IoT Over-the-air Update Library](#aws-iot-over-the-air-update)
        * [AWS IoT Fleet Provisoning](#aws-iot-fleet-provisioning)
        * [AWS SigV4](#aws-sigv4)
        * [backoffAlgorithm](#backoffalgorithm)
    * [Sending metrics to AWS IoT](#sending-metrics-to-aws-iot)
* [Versioning](#versioning)
* [Releases and Documentation](#releases-and-documentation)
    * [202211.00](#20221100)
    * [202108.00](#20210800)
    * [202103.00](#20210300)
    * [202012.01](#20201201)
    * [202011.00](#20201100)
    * [202009.00](#20200900)
    * [v3.1.5](#v315)
* [Porting Guide for 202009.00 and newer releases](#porting-guide-for-20200900-and-newer-releases)
    * [Porting coreMQTT](#porting-coremqtt)
    * [Porting coreHTTP](#porting-corehttp)
    * [Porting AWS IoT Device Shadow](#porting-aws-iot-device-shadow)
    * [Porting AWS IoT Device Defender](#porting-aws-iot-device-defender)
    * [Porting AWS IoT Over-the-air Update](#porting-aws-iot-over-the-air-update)
* [Migration guide from v3.1.5 to 202009.00 and newer releases](#migration-guide-from-v315-to-20200900-and-newer-releases)
    * [MQTT Migration](#mqtt-migration)
    * [Shadow Migration](#shadow-migration)
    * [Jobs Migration](#jobs-migration)
* [Branches](#branches)
    * [main](#main-branch)
    * [v4_beta_deprecated](#v4_beta_deprecated-branch-formerly-named-v4_beta)
* [Getting Started](#getting-started)
    * [Cloning](#cloning)
    * [Configuring Demos](#configuring-demos)
        * [Prerequisites](#prerequisites)
            * [Build Dependencies](#build-dependencies)
        * [AWS IoT Account Setup](#aws-iot-account-setup)
        * [Configuring mutual authentication demos of MQTT and HTTP](#configuring-mutual-authentication-demos-of-mqtt-and-http)
        * [Configuring AWS IoT Device Defender and AWS IoT Device Shadow demos](#configuring-aws-iot-device-defender-and-aws-iot-device-shadow-demos)
        * [Configuring the AWS IoT Fleet Provisioning demo](#configuring-the-aws-iot-fleet-provisioning-demo)
        * [Configuring the S3 demos](#configuring-the-s3-demos)
        * [Setup for AWS IoT Jobs demo](#setup-for-aws-iot-jobs-demo)
        * [Setup for the Greengrass local auth demo](#setup-for-the-greengrass-local-auth-demo)
        * [Prerequisites for the AWS Over-The-Air Update (OTA) demos](#prerequisites-for-the-aws-over-the-air-update-ota-demos)
        * [Scheduling an OTA Update Job](#scheduling-an-ota-update-job)
    * [Building and Running Demos](#building-and-running-demos)
        * [Build a single demo](#build-a-single-demo)
        * [Build all configured demos](#build-all-configured-demos)
        * [Running corePKCS11 demos](#running-corepkcs11-demos)
        * [Alternative option of Docker containers for running demos locally](#alternative-option-of-docker-containers-for-running-demos-locally)
            * [Installing Mosquitto to run MQTT demos locally](#installing-mosquitto-to-run-mqtt-demos-locally)
            * [Installing httpbin to run HTTP demos locally](#installing-httpbin-to-run-http-demos-locally)
* [Generating Documentation](#generating-documentation)

## Overview

The AWS IoT Device SDK for Embedded C (C-SDK) is a collection of C source files under the [MIT open source license](LICENSE) that can be used in embedded applications to securely connect IoT devices to [AWS IoT Core](https://docs.aws.amazon.com/iot/latest/developerguide/what-is-aws-iot.html). It contains MQTT client, HTTP client, JSON Parser, AWS IoT Device Shadow, AWS IoT Jobs, and AWS IoT Device Defender libraries. This SDK is distributed in source form, and can be built into customer firmware along with application code, other libraries and an operating system (OS) of your choice. These libraries are only dependent on standard C libraries, so they can be ported to various OS's - from embedded Real Time Operating Systems (RTOS) to Linux/Mac/Windows. You can find sample usage of C-SDK libraries on POSIX systems using OpenSSL (e.g. [Linux demos](demos) in this repository), and on [FreeRTOS](https://github.com/FreeRTOS/FreeRTOS/) using mbedTLS (e.g. [FreeRTOS demos](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo) in [FreeRTOS](https://github.com/FreeRTOS/FreeRTOS/) repository).

For the latest release of C-SDK, please see the section for [Releases and Documentation](#releases-and-documentation).

**C-SDK includes libraries that are part of the [FreeRTOS 202210.01 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.01-LTS) release. Learn more about the FreeRTOS 202210.01 LTS libraries by [clicking here](https://freertos.org/lts-libraries.html).**

### License

The C-SDK libraries are licensed under the [MIT open source license](LICENSE).

### Features

C-SDK simplifies access to various AWS IoT services. C-SDK has been tested to work with [AWS IoT Core](https://docs.aws.amazon.com/iot/latest/developerguide/what-is-aws-iot.html) and an open source MQTT broker to ensure interoperability. The AWS IoT Device Shadow, AWS IoT Jobs, and AWS IoT Device Defender libraries are flexible to work with any MQTT client and JSON parser. The MQTT client and JSON parser libraries are offered as choices without being tightly coupled with the rest of the SDK. C-SDK contains the following libraries:

#### coreMQTT

The [coreMQTT](https://github.com/FreeRTOS/coreMQTT) library provides the ability to establish an MQTT connection with a broker over a customer-implemented transport layer, which can either be a secure channel like a TLS session (mutually authenticated or server-only authentication) or a non-secure channel like a plaintext TCP connection. This MQTT connection can be used for performing publish operations to MQTT topics and subscribing to MQTT topics. The library provides a mechanism to register customer-defined callbacks for receiving incoming PUBLISH, acknowledgement and keep-alive response events from the broker. The library has been refactored for memory optimization and is compliant with the [MQTT 3.1.1](https://docs.oasis-open.org/mqtt/mqtt/v3.1.1/mqtt-v3.1.1.html) standard. It has no dependencies on any additional libraries other than the standard C library, a customer-implemented network transport interface, and optionally a customer-implemented platform time function. The refactored design embraces different use-cases, ranging from resource-constrained platforms using only QoS 0 MQTT PUBLISH messages to resource-rich platforms using QoS 2 MQTT PUBLISH over TLS connections.

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/coreMQTT/docs/doxygen/output/html/index.html#mqtt_memory_requirements).

#### coreHTTP

The [coreHTTP](https://github.com/FreeRTOS/coreHTTP) library provides the ability to establish an HTTP connection with a server over a customer-implemented transport layer, which can either be a secure channel like a TLS session (mutually authenticated or server-only authentication) or a non-secure channel like a plaintext TCP connection. The HTTP connection can be used to make "GET" (include range requests), "PUT", "POST" and "HEAD" requests. The library provides a mechanism to register a customer-defined callback for receiving parsed header fields in an HTTP response. The library has been refactored for memory optimization, and is a client implementation of a subset of the [HTTP/1.1](https://tools.ietf.org/html/rfc2616) standard.

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/coreHTTP/docs/doxygen/output/html/index.html#http_memory_requirements).

#### coreJSON

The [coreJSON](https://github.com/FreeRTOS/coreJSON) library is a JSON parser that strictly enforces the [ECMA-404 JSON standard](https://www.json.org/json-en.html). It provides a function to validate a JSON document, and a function to search for a key and return its value. A search can descend into nested structures using a compound query key. A JSON document validation also checks for illegal UTF8 encodings and illegal Unicode escape sequences.

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/coreJSON/docs/doxygen/output/html/index.html#json_memory_requirements).

#### corePKCS11

The [corePKCS11](https://github.com/FreeRTOS/corePKCS11) library is an implementation of the PKCS #11 interface (API) that makes it easier to develop applications that rely on cryptographic operations. Only a subset of the [PKCS #11 v2.4](https://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html) standard has been implemented, with a focus on operations involving asymmetric keys, random number generation, and hashing.

The Cryptoki or PKCS #11 standard defines a platform-independent API to manage and use cryptographic tokens. The name, "PKCS #11", is used interchangeably to refer to the API itself and the standard which defines it.

The PKCS #11 API is useful for writing software without taking a dependency on any particular implementation or hardware. By writing against the PKCS #11 standard interface, code can be used interchangeably with multiple algorithms, implementations and hardware.

Generally vendors for secure cryptoprocessors such as Trusted Platform Module ([TPM](https://en.wikipedia.org/wiki/Trusted_Platform_Module)), Hardware Security Module ([HSM](https://en.wikipedia.org/wiki/Hardware_security_module)), Secure Element, or any other type of secure hardware enclave, distribute a PKCS #11 implementation with the hardware.
The purpose of corePKCS11 mock is therefore to provide a PKCS #11 implementation that allows for rapid prototyping and development before switching to a cryptoprocessor specific PKCS #11 implementation in production devices.

Since the PKCS #11 interface is defined as part of the PKCS #11 [specification](https://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html) replacing corePKCS11 with another implementation
should require little porting effort, as the interface will not change. The system tests distributed in corePKCS11 repository can be leveraged to verify the behavior of a different implementation is similar to corePKCS11.

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/corePKCS11/docs/doxygen/output/html/pkcs11_design.html#pkcs11_memory_requirements).

#### AWS IoT Device Shadow

The [AWS IoT Device Shadow](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk) library enables you to store and retrieve the current state one or more shadows of every registered device. A device’s shadow is a persistent, virtual representation of your device that you can interact with from AWS IoT Core even if the device is offline. The device state is captured in its "shadow" is represented as a [JSON](https://www.json.org/) document. The device can send commands over MQTT to get, update and delete its latest state as well as receive notifications over MQTT about changes in its state. The device’s shadow(s) are uniquely identified by the name of the corresponding "thing", a representation of a specific device or logical entity on the AWS Cloud. See [Managing Devices with AWS IoT](https://docs.aws.amazon.com/iot/latest/developerguide/iot-thing-management.html) for more information on IoT "thing". This library supports named shadows, a feature of the AWS IoT Device Shadow service that allows you to create multiple shadows for a single IoT device. More details about AWS IoT Device Shadow can be found in [AWS IoT documentation](https://docs.aws.amazon.com/iot/latest/developerguide/iot-device-shadows.html).

The AWS IoT Device Shadow library has no dependencies on additional libraries other than the standard C library. It also doesn’t have any platform dependencies, such as threading or synchronization. It can be used with any MQTT library and any JSON library (see [demos](demos/shadow) with coreMQTT and coreJSON).

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#shadow_memory_requirements).


#### AWS IoT Jobs

The [AWS IoT Jobs](https://github.com/aws/jobs-for-aws-iot-embedded-sdk) library enables you to interact with the AWS IoT Jobs service which notifies one or more connected devices of a pending “Job”. A Job can be used to manage your fleet of devices, update firmware and security certificates on your devices, or perform administrative tasks such as restarting devices and performing diagnostics. For documentation of the service, please see the [AWS IoT Developer Guide](https://docs.aws.amazon.com/iot/latest/developerguide/iot-jobs.html). Interactions with the Jobs service use the MQTT protocol. This library provides an API to compose and recognize the MQTT topic strings used by the Jobs service.

The AWS IoT Jobs library has no dependencies on additional libraries other than the standard C library. It also doesn’t have any platform dependencies, such as threading or synchronization. It can be used with any MQTT library and any JSON library (see [demos](demos/jobs) with [libmosquitto](https://mosquitto.org/) and coreJSON).

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/jobs-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#jobs_memory_requirements).


#### AWS IoT Device Defender

The [AWS IoT Device Defender](https://github.com/aws/device-defender-for-aws-iot-embedded-sdk) library enables you to interact with the AWS IoT Device Defender service to continuously monitor security metrics from devices for deviations from what you have defined as appropriate behavior for each device. If something doesn’t look right, AWS IoT Device Defender sends out an alert so you can take action to remediate the issue. More details about Device Defender can be found in [AWS IoT Device Defender documentation](https://docs.aws.amazon.com/iot/latest/developerguide/device-defender.html). This library supports custom metrics, a feature that helps you monitor operational health metrics that are unique to your fleet or use case. For example, you can define a new metric to monitor the memory usage or CPU usage on your devices.

The AWS IoT Device Defender library has no dependencies on additional libraries other than the standard C library. It also doesn’t have any platform dependencies, such as threading or synchronization. It can be used with any MQTT library and any JSON library (see [demos](demos/defender) with coreMQTT and coreJSON).

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/device-defender-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#defender_memory_requirements).

#### AWS IoT Over-the-air Update

The [AWS IoT Over-the-air Update](https://github.com/aws/ota-for-aws-iot-embedded-sdk) (OTA) library enables you to manage the notification of a newly available update, download the update, and perform cryptographic verification of the firmware update. Using the OTA library, you can logically separate firmware updates from the application running on your devices. You can also use the library to send other files (e.g. images, certificates) to one or more devices registered with AWS IoT. More details about OTA library can be found in [AWS IoT Over-the-air Update documentation](https://docs.aws.amazon.com/freertos/latest/userguide/freertos-ota-dev.html).

The AWS IoT Over-the-air Update library has a dependency on [coreJSON](https://github.com/FreeRTOS/coreJSON) for parsing of JSON job document and [tinyCBOR](https://github.com/intel/tinycbor.git) for decoding encoded data streams, other than the standard C library. It can be used with any MQTT library, HTTP library, and operating system (e.g. Linux, FreeRTOS) (see [demos](demos/ota) with coreMQTT and coreHTTP over Linux).

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#ota_memory_requirements).

#### AWS IoT Fleet Provisioning

The [AWS IoT Fleet Provisioning](https://github.com/aws/fleet-provisioning-for-aws-iot-embedded-sdk) library enables you to interact with the [AWS IoT Fleet Provisioning MQTT APIs](https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html) in order to provison IoT devices without preexisting device certificates. With AWS IoT Fleet Provisioning, devices can securely receive unique device certificates from AWS IoT when they connect for the first time. For an overview of all provisioning options offered by AWS IoT, see [device provisioning documentation](https://docs.aws.amazon.com/iot/latest/developerguide/iot-provision.html). For details about Fleet Provisioning, refer to the [AWS IoT Fleet Provisioning documentation](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html).

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/fleet-provisioning-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#fleet_provisioning_memory_requirements).

#### AWS SigV4

The [AWS SigV4](https://github.com/aws/SigV4-for-AWS-IoT-embedded-sdk) library enables you to sign HTTP requests with [Signature Version 4 Signing Process](https://docs.aws.amazon.com/general/latest/gr/signature-version-4.html). Signature Version 4 (SigV4) is the process to add authentication information to HTTP requests to AWS services. For security, most requests to AWS must be signed with an access key. The access key consists of an access key ID and secret access key.

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/sigv4-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#sigv4_memory_requirements).

#### backoffAlgorithm

The [backoffAlgorithm](https://github.com/FreeRTOS/backoffAlgorithm) library is a utility library to calculate backoff period using an exponential backoff with jitter algorithm for retrying network operations (like failed network connection with server). This library uses the "Full Jitter" strategy for the exponential backoff with jitter algorithm. More information about the algorithm can be seen in the [Exponential Backoff and Jitter AWS blog](https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/).

Exponential backoff with jitter is typically used when retrying a failed connection or network request to the server. An exponential backoff with jitter helps to mitigate the failed network operations with servers, that are caused due to network congestion or high load on the server, by spreading out retry requests across multiple devices attempting network operations. Besides, in an environment with poor connectivity, a client can get disconnected at any time. A backoff strategy helps the client to conserve battery by not repeatedly attempting reconnections when they are unlikely to succeed.

The backoffAlgorithm library has no dependencies on libraries other than the standard C library.

See memory requirements for the latest release [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/backoffAlgorithm/docs/doxygen/output/html/index.html#backoff_algorithm_memory_requirements).

### Sending metrics to AWS IoT

When establishing a connection with AWS IoT, users can optionally report the Operating System, Hardware Platform and MQTT client version information of their device to AWS. This information can help AWS IoT provide faster issue resolution and technical support. If users want to report this information, they can send a specially formatted string (see below) in the username field of the MQTT CONNECT packet.

Format

The format of the username string with metrics is:

```
<Actual_Username>?SDK=<OS_Name>&Version=<OS_Version>&Platform=<Hardware_Platform>&MQTTLib=<MQTT_Library_name>@<MQTT_Library_version>
```

Where

* <Actual_Username> is the actual username used for authentication, if username and password are used for authentication. When username and password based authentication is not used, this
is an empty value.
* <OS_Name> is the Operating System the application is running on (e.g. Ubuntu)
* <OS_Version> is the version number of the Operating System (e.g. 20.10)
* <Hardware_Platform> is the Hardware Platform the application is running on (e.g. RaspberryPi)
* <MQTT_Library_name> is the MQTT Client library being used (e.g. coreMQTT)
* <MQTT_Library_version> is the version of the MQTT Client library being used (e.g. 1.1.0)

Example

*  Actual_Username = “iotuser”, OS_Name = Ubuntu, OS_Version = 20.10, Hardware_Platform_Name = RaspberryPi, MQTT_Library_Name = coremqtt, MQTT_Library_version = 1.1.0. If username is not used, then “iotuser” can be removed.

```
/* Username string:
 * iotuser?SDK=Ubuntu&Version=20.10&Platform=RaspberryPi&MQTTLib=coremqtt@1.1.0
 */

#define OS_NAME                   "Ubuntu"
#define OS_VERSION                "20.10"
#define HARDWARE_PLATFORM_NAME    "RaspberryPi"
#define MQTT_LIB                  "coremqtt@1.1.0"

#define USERNAME_STRING           "iotuser?SDK=" OS_NAME "&Version=" OS_VERSION "&Platform=" HARDWARE_PLATFORM_NAME "&MQTTLib=" MQTT_LIB
#define USERNAME_STRING_LENGTH    ( ( uint16_t ) ( sizeof( USERNAME_STRING ) - 1 ) )

MQTTConnectInfo_t connectInfo;
connectInfo.pUserName = USERNAME_STRING;
connectInfo.userNameLength = USERNAME_STRING_LENGTH;
mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, pSessionPresent );
```

## Versioning

C-SDK releases will now follow a date based versioning scheme with the format YYYYMM.NN, where:

* Y represents the year.
* M represents the month.
* N represents the release order within the designated month (00 being the first release).

For example, a second release in June 2021 would be 202106.01. Although the SDK releases have moved to date-based versioning, each library within the SDK will still retain semantic versioning. In semantic versioning, the version number itself (X.Y.Z) indicates whether the release is a major, minor, or point release. You can use the semantic version of a library to assess the scope and impact of a new release on your application.

## Releases and Documentation

All of the released versions of the C-SDK libraries are available as git tags. For example, the last release of the v3 SDK version is available at [tag 3.1.5](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v3.1.5).

### 202211.00
[API documentation of 202211.00 release](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/index.html)

This release includes an update to how the [Coverity static analysis](https://scan.coverity.com/) scans are performed. There is now a **tools/coverity/README.md** file in each library with instructions on how to perform a scan with 0 [MISRA coding standard](https://www.misra.org.uk) warnings or errors.

Additionally, this release brings in major version upgrades to [coreMQTT](https://github.com/FreeRTOS/coreMQTT) and [coreHTTP](https://github.com/FreeRTOS/coreHTTP). It also brings in minor version upgrades to all other libraries.

### 202108.00

[API documentation of 202108.00 release](https://aws.github.io/aws-iot-device-sdk-embedded-C/202108.00/index.html)

This release introduces the refactored [AWS IoT Fleet Provisioning](https://github.com/aws/fleet-provisioning-for-aws-iot-embedded-sdk) library and the new [AWS SigV4](https://github.com/aws/SigV4-for-AWS-IoT-embedded-sdk) library.

Additionally, this release brings minor version updates in the [AWS IoT Over-the-Air Update](https://github.com/aws/ota-for-aws-iot-embedded-sdk) and [corePKCS11](https://github.com/FreeRTOS/corePKCS11) libraries.

### 202103.00

[API documentation of 202103.00 release](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/index.html)

This release includes a [major update](https://github.com/aws/ota-for-aws-iot-embedded-sdk/blob/v3.0.0/CHANGELOG.md#v300-march-2021) to the APIs of the AWS IoT Over-the-air Update library.

Additionally, AWS IoT Device Shadow library introduces a [minor update](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/blob/v1.1.0/CHANGELOG.md#v110-march-2021) by adding support for named shadow, a feature of the AWS IoT Device Shadow service that allows you to create multiple shadows for a single IoT device. AWS IoT Jobs library introduces a [minor update](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/blob/v1.1.0/CHANGELOG.md#v110-march-2021) by introducing macros for `$next` job ID and compile-time generation of topic strings. AWS IoT Device Defender library introduces a [minor update](https://github.com/aws/Device-Defender-for-AWS-IoT-embedded-sdk/blob/v1.1.0/CHANGELOG.md#v110-march-2021) that adds macros to API for custom metrics feature of AWS IoT Device Defender service.

corePKCS11 also introduces a [patch update](https://github.com/FreeRTOS/corePKCS11/blob/v3.0.1/CHANGELOG.md#v301-february-2021) by removing the `pkcs11configPAL_DESTROY_SUPPORTED` config and mbedTLS platform abstraction layer of `DestroyObject`. Lastly, no code changes are introduced for backoffAlgorithm, coreHTTP, coreMQTT, and coreJSON; however, patch updates are made to improve documentation and CI.

### 202012.01

[API documentation of 202012.01 release](https://docs.aws.amazon.com/embedded-csdk/202012.00/lib-ref/index.html)

This release includes [AWS IoT Over-the-air Update(Release Candidate)](https://github.com/aws/ota-for-aws-iot-embedded-sdk), [backoffAlgorithm](https://github.com/FreeRTOS/backoffAlgorithm), and [PKCS #11](https://github.com/FreeRTOS/corePKCS11) libraries. Additionally, there is a major update to the coreJSON and coreHTTP APIs. All libraries continue to undergo code quality checks (e.g. MISRA-C compliance), and Coverity static analysis. In addition, all libraries except AWS IoT Over-the-air Update and backoffAlgorithm undergo validation of memory safety with the C Bounded Model Checker (CBMC) automated reasoning tool.

### 202011.00

[API documentation of 202011.00 release](https://docs.aws.amazon.com/embedded-csdk/202011.00/lib-ref/index.html)

This release includes refactored HTTP client, AWS IoT Device Defender, and AWS IoT Jobs libraries. Additionally, there is a major update to the coreJSON API. All libraries continue to undergo code quality checks (e.g. MISRA-C compliance), Coverity static analysis, and validation of memory safety with the C Bounded Model Checker (CBMC) automated reasoning tool.

### 202009.00

[API documentation of 202009.00 release](https://docs.aws.amazon.com/freertos/latest/lib-ref/embedded-csdk/202009.00/lib-ref/index.html)

This release includes refactored MQTT, JSON Parser, and AWS IoT Device Shadow libraries for optimized memory usage and modularity. These libraries are included in the SDK via [Git submoduling](https://git-scm.com/book/en/v2/Git-Tools-Submodules). These libraries have gone through code quality checks including verification that no function has a [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html) score over 8, and checks against deviations from mandatory rules in the [MISRA coding standard](https://www.misra.org.uk). Deviations from the MISRA C:2012 guidelines are documented under [MISRA Deviations](MISRA.md). These libraries have also undergone both static code analysis from [Coverity static analysis](https://scan.coverity.com/), and validation of memory safety and data structure invariance through the [CBMC automated reasoning tool](https://www.cprover.org/cbmc/).

If you are upgrading from v3.x API of the C-SDK to the 202009.00 release, please refer to [Migration guide from v3.1.5 to 202009.00 and newer releases](#migration-guide-from-v315-to-20200900-and-newer-releases). If you are using the C-SDK v4_beta_deprecated branch, note that we will continue to maintain this branch for critical bug fixes and security patches but will not add new features to it. See the C-SDK v4_beta_deprecated branch [README](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/v4_beta_deprecated/README.md) for additional details.

### v3.1.5

Details available [here](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v3.1.5).

## Porting Guide for 202009.00 and newer releases

All libraries depend on the ISO C90 standard library and additionally on the `stdint.h` library for fixed-width integers, including `uint8_t`, `int8_t`, `uint16_t`, `uint32_t` and `int32_t`, and constant macros like `UINT16_MAX`. If your platform does not support the `stdint.h` library, definitions of the mentioned fixed-width integer types will be required for porting any C-SDK library to your platform.

### Porting coreMQTT

Guide for porting coreMQTT library to your platform is available [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/coreMQTT/docs/doxygen/output/html/mqtt_porting.html).

### Porting coreHTTP

Guide for porting coreHTTP library is available [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/standard/coreHTTP/docs/doxygen/output/html/http_porting.html).

### Porting AWS IoT Device Shadow

Guide for porting AWS IoT Device Shadow library is available [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/docs/doxygen/output/html/shadow_porting.html).

### Porting AWS IoT Device Defender

Guide for porting AWS IoT Device Defender library is available [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/device-defender-for-aws-iot-embedded-sdk/docs/doxygen/output/html/defender_porting.html).

### Porting AWS IoT Over-the-air Update

Guide for porting OTA library to your platform is available [here](https://aws.github.io/aws-iot-device-sdk-embedded-C/202211.00/libraries/aws/ota-for-aws-iot-embedded-sdk/docs/doxygen/output/html/ota_porting.html).

## Migration guide from v3.1.5 to 202009.00 and newer releases

### MQTT Migration

Migration guide for MQTT library is available [here](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/docs/doxygen/output/html/mqtt_migration.html).

### Shadow Migration

Migration guide for Shadow library is available [here](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/docs/doxygen/output/html/shadow_migration.html).

### Jobs Migration

Migration guide for Jobs library is available [here](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/docs/doxygen/output/html/jobs_migration.html).

## Branches

### main branch

The [main](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main) branch hosts the continuous development of the AWS IoT Embedded C SDK (C-SDK) libraries. Please be aware that the development at the tip of the main branch is continuously in progress, and may have bugs. Consider using the [tagged releases](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases) of the C-SDK for production ready software.

### v4_beta_deprecated branch (formerly named v4_beta)

The [v4_beta_deprecated](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta_deprecated) branch contains a beta version of the C-SDK libraries, which is now deprecated. This branch was earlier named as v4_beta, and was renamed to v4_beta_deprecated. The libraries in this branch will not be released. However, critical bugs will be fixed and tested. No new features will be added to this branch.

## Getting Started

### Cloning

This repository uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in the C-SDK libraries (eg, MQTT ) and third-party dependencies (eg, mbedtls for POSIX platform transport layer).
Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules (The ZIP file is also not a valid git repository). If you download from the [202012.00 Release Page](https://github.com/aws/aws-iot-device-sdk-embedded-C/releases/tag/202012.00) page, you will get the entire repository (including the submodules) in the ZIP file, aws-iot-device-sdk-embedded-c-202012.00.zip.
To clone the latest commit to main branch using HTTPS:

```sh
git clone --recurse-submodules https://github.com/aws/aws-iot-device-sdk-embedded-C.git
```

Using SSH:

```sh
git clone --recurse-submodules git@github.com:aws/aws-iot-device-sdk-embedded-C.git
```

If you have downloaded the repo without using the `--recurse-submodules` argument, you need to run:

```sh
git submodule update --init --recursive
```

When building with CMake, submodules are also recursively cloned automatically. However, `-DBUILD_CLONE_SUBMODULES=0`
can be passed as a CMake flag to disable this functionality. This is useful when you'd like to build CMake while using a
different commit from a submodule.

### Configuring Demos

The libraries in this SDK are not dependent on any operating system. However, the demos for the libraries in this SDK are built and tested on a Linux platform. The demos build with [CMake](https://cmake.org/), a cross-platform build tool.

#### Prerequisites

* CMake 3.2.0 or any newer version for utilizing the build system of the repository.
* C90 compiler such as gcc
    * Due to the use of mbedtls in corePKCS11, a C99 compiler is required if building the PKCS11 demos.
* Although not a part of the ISO C90 standard, `stdint.h` is required for fixed-width integer types that include `uint8_t`, `int8_t`, `uint16_t`, `uint32_t` and `int32_t`, and constant macros like `UINT16_MAX`, while `stdbool.h` is required for boolean parameters in coreMQTT. For compilers that do not provide these header files, [coreMQTT](https://github.com/FreeRTOS/coreMQTT) provides the files [stdint.readme](https://github.com/FreeRTOS/coreMQTT/blob/main/source/include/stdint.readme) and [stdbool.readme](https://github.com/FreeRTOS/coreMQTT/blob/main/source/include/stdbool.readme), which can be renamed to `stdint.h` and `stdbool.h`, respectively, to provide the required type definitions.
* A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems.
    * Linux system with POSIX sockets, threads, RT, and timer APIs. (We have tested on Ubuntu 18.04).

##### Build Dependencies

The follow table shows libraries that need to be installed in your system to run certain demos. If a dependency is
not installed and cannot be built from source, demos that require that dependency will be excluded
from the default `all` target.

Dependency | Version | Usage
:---: | :---: | :---:
[OpenSSL](https://github.com/openssl/openssl) | 1.1.0 or later | All TLS demos and tests with the exception of PKCS11
[Mosquitto Client](https://github.com/eclipse/mosquitto) | 1.4.10 or later | AWS IoT Jobs Mosquitto demo

#### AWS IoT Account Setup

You need to setup an AWS account and access the AWS IoT console for running the AWS IoT Device Shadow library, AWS IoT Device Defender library, AWS IoT Jobs library,
AWS IoT OTA library and coreHTTP S3 download demos.
Also, the AWS account can be used for running the MQTT mutual auth demo against AWS IoT broker.
Note that running the AWS IoT Device Defender, AWS IoT Jobs and AWS IoT Device Shadow library demos require the setup of a Thing resource for the device running the demo.
Follow the links to:
- [Setup an AWS account](https://portal.aws.amazon.com/billing/signup#/start).
- [Sign-in to the AWS IoT Console](https://console.aws.amazon.com/iot/home) after setting up the AWS account.
- [Create a Thing resource](https://docs.aws.amazon.com/iot/latest/developerguide/iot-moisture-create-thing.html).

The MQTT Mutual Authentication and AWS IoT Shadow demos include example AWS IoT policy documents to run each respective demo with AWS IoT. You may use the [MQTT Mutual auth](./demos/mqtt/mqtt_demo_mutual_auth/aws_iot_policy_example_mqtt.json) and [Shadow](./demos/shadow/shadow_demo_main/aws_iot_policy_example_shadow.json) example policies by replacing `[AWS_REGION]` and `[AWS_ACCOUNT_ID]` with the strings of your region and account identifier. While the IoT Thing name and MQTT client identifier do not need to match for the demos to run, the example policies have the Thing name and client identifier identical as per [AWS IoT best practices](https://docs.aws.amazon.com/iot/latest/developerguide/security-best-practices.html).

It can be very helpful to also have the [AWS Command Line Interface tooling](https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-install.html) installed.

#### Configuring mutual authentication demos of MQTT and HTTP

You can pass the following configuration settings as command line options in order to run the mutual auth demos. Make sure to run the following command in the root directory of the C-SDK:

```sh
## optionally find your-aws-iot-endpoint from the command line
aws iot describe-endpoint --endpoint-type iot:Data-ATS
cmake -S . -Bbuild
-DAWS_IOT_ENDPOINT="<your-aws-iot-endpoint>" -DCLIENT_CERT_PATH="<your-client-certificate-path>" -DCLIENT_PRIVATE_KEY_PATH="<your-client-private-key-path>"
```

In order to set these configurations manually, edit `demo_config.h` in `demos/mqtt/mqtt_demo_mutual_auth/` and `demos/http/http_demo_mutual_auth/` to `#define` the following:

* Set `AWS_IOT_ENDPOINT` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.<aws-region>.amazonaws.com` where `<aws-region>` can be an AWS region like `us-east-2`.
   * Optionally, it can also be found with the AWS CLI command `aws iot describe-endpoint --endpoint-type iot:Data-ATS`.
* Set `CLIENT_CERT_PATH` to the path of the client certificate downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).
* Set `CLIENT_PRIVATE_KEY_PATH` to the path of the private key downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).

It is possible to configure `ROOT_CA_CERT_PATH` to any PEM-encoded Root CA Certificate.
However, this is optional because CMake will download and set it to [AmazonRootCA1.pem](https://www.amazontrust.com/repository/AmazonRootCA1.pem) when unspecified.
If unspecified, the default Root CA path will be interpreted relative to where the demo binary is executed.
For many demos, you can change this path by modifying it in the corresponding `demo_config.h`.

#### Configuring AWS IoT Device Defender and AWS IoT Device Shadow demos

To build the AWS IoT Device Defender and AWS IoT Device Shadow demos, you can pass the following configuration settings as command line options. Make sure to run the following command in the root directory of the C-SDK:

```sh
cmake -S . -Bbuild -DAWS_IOT_ENDPOINT="<your-aws-iot-endpoint>" -DROOT_CA_CERT_PATH="<your-path-to-amazon-root-ca>" -DCLIENT_CERT_PATH="<your-client-certificate-path>" -DCLIENT_PRIVATE_KEY_PATH="<your-client-private-key-path>" -DTHING_NAME="<your-registered-thing-name>"
```

An Amazon Root CA certificate can be downloaded from [here](https://www.amazontrust.com/repository/).

In order to set these configurations manually, edit `demo_config.h` in the demo folder to `#define` the following:

* Set `AWS_IOT_ENDPOINT` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`.
* Set `ROOT_CA_CERT_PATH` to the path of the root CA certificate downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).
* Set `CLIENT_CERT_PATH` to the path of the client certificate downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).
* Set `CLIENT_PRIVATE_KEY_PATH` to the path of the private key downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).
* Set `THING_NAME` to the name of the Thing created in [AWS IoT Account Setup](#aws-iot-account-setup).

#### Configuring the AWS IoT Fleet Provisioning demo

To build the AWS IoT Fleet Provisioning Demo, you can pass the following configuration settings as command line options. Make sure to run the following command in the root directory of the C-SDK:

```sh
cmake -S . -Bbuild -DAWS_IOT_ENDPOINT="<your-aws-iot-endpoint>" -DROOT_CA_CERT_PATH="<your-path-to-amazon-root-ca>" -DCLAIM_CERT_PATH="<your-claim-certificate-path>" -DCLAIM_PRIVATE_KEY_PATH="<your-claim-private-key-path>" -DPROVISIONING_TEMPLATE_NAME="<your-template-name>" -DDEVICE_SERIAL_NUMBER="<your-serial-number>"
```

An Amazon Root CA certificate can be downloaded from [here](https://www.amazontrust.com/repository/).

To create a provisioning template and claim credentials, sign into your AWS account and visit [here][create_provtemplate]. Make sure to enable the "Use the AWS IoT registry to manage your device fleet" option. Once
you have created the template and credentials, modify the claim certificate's policy to match the [sample policy][sample_claim_policy].

In order to set these configurations manually, edit `demo_config.h` in the demo folder to `#define` the following:

* Set `AWS_IOT_ENDPOINT` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`.
* Set `ROOT_CA_CERT_PATH` to the path of the root CA certificate downloaded when setting up the device certificate in [AWS IoT Account Setup](#aws-iot-account-setup).
* Set `CLAIM_CERT_PATH` to the path of the claim certificate downloaded when setting up the template and claim credentials.
* Set `CLAIM_PRIVATE_KEY_PATH` to the path of the private key downloaded when setting up the template and claim credentials.
* Set `PROVISIONING_TEMPLATE_NAME` to the name of the provisioning template created.
* Set `DEVICE_SERIAL_NUMBER` to an arbitrary string representing a device identifier.

[create_provtemplate]: https://console.aws.amazon.com/iot/home#/provisioningtemplate/create/instruction
[sample_claim_policy]: demos/fleet_provisioning/fleet_provisioning_with_csr/example_claim_policy.json

#### Configuring the S3 demos

You can pass the following configuration settings as command line options in order to run the S3 demos. Make sure to run the following command in the root directory of the C-SDK:

```sh
cmake -S . -Bbuild -DS3_PRESIGNED_GET_URL="s3-get-url" -DS3_PRESIGNED_PUT_URL="s3-put-url"
```

`S3_PRESIGNED_PUT_URL` is only needed for the S3 upload demo.

In order to set these configurations manually, edit `demo_config.h` in `demos/http/http_demo_s3_download_multithreaded`, and `demos/http/http_demo_s3_upload` to `#define` the following:

* Set `S3_PRESIGNED_GET_URL` to a S3 presigned URL with GET access.
* Set `S3_PRESIGNED_PUT_URL` to a S3 presigned URL with PUT access.

You can generate the presigned urls using [demos/http/common/src/presigned_urls_gen.py](demos/http/common/src/presigned_urls_gen.py). More info can be found [here](demos/http/common/src/README.md).

####  Configure S3 Download HTTP Demo using SigV4 Library:

Refer this [demos/http/http_demo_s3_download/README.md](demos/http/http_demo_s3_download/README.md) to follow the steps needed to configure and run the S3 Download HTTP Demo using SigV4 Library that generates the authorization HTTP header needed to authenticate the HTTP requests send to S3.

#### Setup for AWS IoT Jobs demo

1. The demo requires the Linux platform to contain curl and libmosquitto. On a Debian platform, these dependencies can be installed with:

```
    apt install curl libmosquitto-dev
```
If the platform does not contain the `libmosquitto` library, the demo will build the library from source.

`libmosquitto` 1.4.10 or any later version of the first major release is required to run this demo.

2. A job that specifies the URL to download for the demo needs to be created on the AWS account for the Thing resource that will be used by the demo.
The job can be created directly from the [AWS IoT console](https://console.aws.amazon.com/iot/home) or using the aws cli tool.

The following creates a job that specifies a Linux Kernel link for downloading.

```
 aws iot create-job \
        --job-id 'job_1' \
        --targets arn:aws:iot:us-west-2:<account-id>:thing/<thing-name> \
        --document '{"url":"https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.8.5.tar.xz"}'
```

#### Setup for the Greengrass local auth demo

For setting up the Greengrass local auth demo, see [the README in the demo folder](./demos/greengrass/greengrass_demo_local_auth/README.md).

#### Prerequisites for the AWS Over-The-Air Update (OTA) demos

1. To perform a successful OTA update, you need to complete the prerequisites mentioned [here](https://docs.aws.amazon.com/freertos/latest/userguide/ota-prereqs.html).
1. A code signing certificate is required to authenticate the update. A code signing certificate based on the SHA-256 ECDSA algorithm will work with the current demos. An example of how to generate this kind of certificate can be found [here](https://docs.aws.amazon.com/freertos/latest/userguide/ota-code-sign-cert-esp.html).
1. The code signing certificate can be either baked into firmware as a string, or stored as a file.
    1. For baked in certificate method, copy the certificate to signingcredentialSIGNING_CERTIFICATE_PEM in [ota_pal_posix.c](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/main/platform/posix/ota_pal/source/ota_pal_posix.c).
    2. For file storage method, store the certificate as a file and supply the file path in "Path name of code signing certificate on device" field when creating the OTA job in AWS IoT Console.

#### Scheduling an OTA Update Job

After you build and run the initial executable you will have to create another executable and schedule an OTA update job with this image.
1. Increase the version of the application by setting macro `APP_VERSION_BUILD` in `demos/ota/ota_demo_core_[mqtt/http]/demo_config.h` to a different version than what is running.
1. Rebuild the application using the [build steps](#building-and-running-demos) below into a different directory, say `build-dir-2`.
1. Rename the demo executable to reflect the change, e.g. `mv ota_demo_core_mqtt ota_demo_core_mqtt2`
1. Create an OTA job:
    1. Go to the [AWS IoT Core console](https://console.aws.amazon.com/iot/).
    1. Manage → Jobs → Create → Create a FreeRTOS OTA update job → Select the corresponding name for your device from the thing list.
    1. Sign a new firmware → Create a new profile → Select any SHA-ECDSA signing platform → Upload the code signing certificate(from prerequisites) and provide its path on the device.
    1. Select the image → Select the bucket you created during the [prerequisite steps](#prerequisites-for-the-aws-over-the-air-update-ota-demos) → Upload the binary `build-dir-2/bin/ota_demo2`.
    1. The path on device should be the absolute path to place the executable and the binary name: e.g. `/home/ubuntu/aws-iot-device-sdk-embedded-C-staging/build-dir/bin/ota_demo_core_mqtt2`.
    1. Select the IAM role created during the [prerequisite steps](#prerequisites-for-the-aws-over-the-air-update-ota-demos).
    1. Create the Job.
1. Run the initial executable again with the following command: `sudo ./ota_demo_core_mqtt` or `sudo ./ota_demo_core_http`.
1. After the initial executable has finished running, go to the directory where the downloaded firmware image resides which is the path name used when creating an OTA job.
1. Change the permissions of the downloaded firmware to make it executable, as it may be downloaded with read (user default) permissions only: `chmod 775 ota_demo_core_mqtt2`
1. Run the downloaded firmware image with the following command: `sudo ./ota_demo_core_mqtt2`

### Building and Running Demos

Before building the demos, ensure you have installed the [prerequisite software](#prerequisites). On Ubuntu 18.04 and 20.04, `gcc`, `cmake`, and OpenSSL can be installed with:
```sh
sudo apt install build-essential cmake libssl-dev
```

#### Build a single demo
* Go to the root directory of the C-SDK.
* Run *cmake* to generate the Makefiles: `cmake -S . -Bbuild && cd build`
* Choose a demo from the list below or alternatively, run `make help | grep demo`:
```
defender_demo
http_demo_basic_tls
http_demo_mutual_auth
http_demo_plaintext
http_demo_s3_download
http_demo_s3_download_multithreaded
http_demo_s3_upload
jobs_demo_mosquitto
mqtt_demo_basic_tls
mqtt_demo_mutual_auth
mqtt_demo_plaintext
mqtt_demo_serializer
mqtt_demo_subscription_manager
ota_demo_core_http
ota_demo_core_mqtt
pkcs11_demo_management_and_rng
pkcs11_demo_mechanisms_and_digests
pkcs11_demo_objects
pkcs11_demo_sign_and_verify
shadow_demo_main
```
* Replace `demo_name` with your desired demo then build it: `make demo_name`
* Go to the `build/bin` directory and run any demo executables from there.

#### Build all configured demos
* Go to the root directory of the C-SDK.
* Run *cmake* to generate the Makefiles: `cmake -S . -Bbuild && cd build`
* Run this command to build all configured demos: `make`
* Go to the `build/bin` directory and run any demo executables from there.

#### Running corePKCS11 demos

The corePKCS11 demos do not require any AWS IoT resources setup, and are standalone. The demos build upon each other to introduce concepts in PKCS #11 sequentially. Below is the recommended order.
1. `pkcs11_demo_management_and_rng`
1. `pkcs11_demo_mechanisms_and_digests`
1. `pkcs11_demo_objects`
1. `pkcs11_demo_sign_and_verify`
    1. Please note that this demo requires the private and public key generated from `pkcs11_demo_objects` to be in the directory the demo is executed from.

#### Alternative option of Docker containers for running demos locally

Install Docker:

```sh
curl -fsSL https://get.docker.com -o get-docker.sh

sh get-docker.sh
```

##### Installing Mosquitto to run MQTT demos locally

The following instructions have been tested on an Ubuntu 18.04 environment with Docker and OpenSSL installed.

1. Download the official Docker image for Mosquitto 1.6.14. This version is deliberately chosen so that the Docker container can load certificates from the host system.
Any version after 1.6.14 will drop privileges as soon as the configuration file has been read (before TLS certificates are loaded).

    ```sh
    docker pull eclipse-mosquitto:1.6.14
    ```

1. If a Mosquitto broker with TLS communication needs to be run, ignore this step and proceed to the next step. A Mosquitto broker with plain text communication can be run by executing the command below.

    ```
    docker run -it -p 1883:1883 --name mosquitto-plain-text eclipse-mosquitto:1.6.14
    ```

1. Set `BROKER_ENDPOINT` defined in `demos/mqtt/mqtt_demo_plaintext/demo_config.h` to `localhost`.

    Ignore the remaining steps unless a Mosquitto broker with TLS communication also needs to be run.

1. For TLS communication with Mosquitto broker, server and CA credentials need to be created. Use OpenSSL commands to generate the credentials for the Mosquitto server.

    Note: Make sure to use different Common Name (CN) detail between the CA and server certificates; otherwise, SSL handshake fails with exactly same Common Name (CN) detail in both the certificates.

    ```sh
    # Generate CA key and certificate. Provide the Subject field information as appropriate for CA certificate.
    openssl req -x509 -nodes -sha256 -days 365 -newkey rsa:2048 -keyout ca.key -out ca.crt
    ```

    ```sh
    # Generate server key and certificate.# Provide the Subject field information as appropriate for Server certificate. Make sure the Common Name (CN) field is different from the root CA certificate.
    openssl req -nodes -sha256 -new -keyout server.key -out server.csr # Sign with the CA cert.
    openssl x509 -req -sha256 -in server.csr -CA ca.crt -CAkey ca.key -CAcreateserial -out server.crt -days 365
    ```

1. Create a mosquitto.conf file to use port 8883 (for TLS communication) and providing path to the generated credentials.

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

1. Run the docker container from the local directory containing the generated credential and mosquitto.conf files.

    ```sh
    docker run -it -p 8883:8883 -v $(pwd):/mosquitto/config/ --name mosquitto-basic-tls eclipse-mosquitto:1.6.14
    ```

1. Update `demos/mqtt/mqtt_demo_basic_tls/demo_config.h` to the following:
   Set `BROKER_ENDPOINT` to `localhost`.
   Set `ROOT_CA_CERT_PATH` to the absolute path of the CA certificate created in step 4. for the local Mosquitto server.

##### Installing httpbin to run HTTP demos locally

Run httpbin through port 80:

```sh
docker pull kennethreitz/httpbin
docker run -p 80:80 kennethreitz/httpbin
```

`SERVER_HOST` defined in `demos/http/http_demo_plaintext/demo_config.h` can now be set to `localhost`.

To run `http_demo_basic_tls`, you could use either [Tunnelmole](https://github.com/robbie-cahill/tunnelmole-client), an open source tunneling tool, or [ngrok](https://ngrok.com/download), a popular closed source tunneling tool, to create an HTTPS tunnel to the httpbin server currently hosted on port 80:

**Using Tunnelmole**
First, install Tunnelmole. On Linux, Mac and Windows Subsystem for Linux, use

```sh
curl -O https://tunnelmole.com/sh/install.sh && sudo bash install.sh
```

For Windows without WSL, [download tmole.exe](https://tunnelmole.com/downloads/tmole.exe) and add it to your [PATH](https://www.wikihow.com/Change-the-PATH-Environment-Variable-on-Windows).

Then run `tmole 80`

```sh
tmole 80
```

Tunnelmole will provide a https link that can be substituted in `demos/http/http_demo_basic_tls/demo_config.h` and has a format of `https://bvdo5f-ip-49-183-170-144.tunnelmole.net`.

Set `SERVER_HOST` in `demos/http/http_demo_basic_tls/demo_config.h` to the https link provided by Tunnelmole, without `https://` preceding it.

**Using ngrok**

```sh
./ngrok http 80 # May have to use ./ngrok.exe depending on OS or filename of the executable
```

`ngrok` will provide an https link that can be substituted in `demos/http/http_demo_basic_tls/demo_config.h` and has a format of `https://ABCDEFG12345.ngrok.io`.

Set `SERVER_HOST` in `demos/http/http_demo_basic_tls/demo_config.h` to the https link provided by ngrok, without `https://` preceding it.

You must also download the Root CA certificate provided by the ngrok https link and set `ROOT_CA_CERT_PATH` in `demos/http/http_demo_basic_tls/demo_config.h` to the file path of the downloaded certificate.

## Generating Documentation
Note: For pre-generated documentation, please visit [Releases and Documentation](#releases-and-documentation) section.

The Doxygen references were created using Doxygen version 1.9.2. To generate the Doxygen pages, use the provided Python script at [tools/doxygen/generate_docs.py](tools/doxygen/generate_docs.py). Please ensure that each of the library submodules under `libraries/standard/` and `libraries/aws/` are cloned before using this script.

```sh
cd <CSDK_ROOT>
git submodule update --init --recursive --checkout
python3 tools/doxygen/generate_docs.py
```

The generated documentation landing page is located at `docs/doxygen/output/html/index.html`.
