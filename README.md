
# AWS IoT Device SDK C 202009.00

**[Link to API documentation]**    (LINK REQUIRED)

We have released version 202009.00 of the AWS IoT SDK for Embedded-C (C-SDK). This release contains refactored libraries, and is a new design from the C-SDK v3.x. This release includes refactored MQTT and AWS IoT Device Shadow libraries for memory usage and modularity, and includes dependent libraries via GitHub submoduling. These libraries have gone through code quality checks including for [GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html), [MISRA coding standard](https://www.misra.org.uk/MISRAHome/MISRAC2012/tabid/196/Default.aspx), [Coverity statical analysis](https://scan.coverity.com/), and [AWS CBMC automated reasoning tool](https://www.youtube.com/watch?v=YwQHAPRhQkI&feature=youtu.be&t=1721) to ensure memory safety, thread safety and functional correctness proof.   
  
If you are upgrading from v3.x of the C-SDK to the 202009.00 release, please follow the update guide (LINK REQUIRED). If you are using the C-SDK v4_beta_deprecated branch, note that we will continue to fix bugs but will not add new features to it. See the C-SDK v4_beta branch [README](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/v4_beta_deprecated/README.md) for additional details. 

## Overview

The AWS IoT Device SDK for Embedded C (C-SDK) is a collection of C source files under the [MIT open source license](LICENSE) that can be used in embedded applications to securely connect IoT devices to [AWS IoT Core](http://docs.aws.amazon.com/iot/latest/developerguide/what-is-aws-iot.html). It includes transport clients MQTT, TLS implementations, and examples for their use. It also supports AWS IoT specific features such as Device Shadow. It is distributed in source form and intended to be built into customer firmware along with application code, other libraries and RTOS. For additional information about porting the C-SDK onto additional platforms, see the [Porting Guide](https://github.com/aws/aws-iot-device-sdk-embedded-c/blob/master/PortingGuide.md/).

## Features

The Device SDK simplifies access to the Pub/Sub functionality of the AWS IoT broker via MQTT and provide APIs to interact with Device Shadow. The SDK has been tested to work with the AWS IoT Core to ensure best interoperability of a device with the AWS IoT platform. C-SDK contains the following libraries:

### MQTT 
The Device SDK provides functionality to create and maintain a mutually authenticated TLS connection over which it runs MQTT. This connection is used for any further publish operations and allow for subscribing to MQTT topics which will call a configurable callback function when these topics are received.  The [coreMQTT](https://github.com/FreeRTOS/coreMQTT) Client library has been refactored for memory optimization and implements the complete [MQTT 3.1.1](http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/mqtt-v3.1.1.html) standard.  It has no dependencies on any additional libraries other than the standard C library and a customer-implemented network transport interface.  The refactored design embraces different use-cases, ranging from resource-constrained platforms using only QoS 0 MQTT PUBLISH messages to resource-rich platforms using QoS 2 MQTT PUBLISH over TLS connections.  

### AWS IoT Device Shadow
The [AWS IoT Device Shadow](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk) enables you to store and retrieve the current state (the “shadow”) of every registered device. The device’s shadow is a persistent, virtual representation of your device that you can interact with in your applications even if the device is offline. The device state captured as its “shadow” is itself a [JSON](https://www.json.org/) document. You can send commands over MQTT or HTTP to query the latest known device state, or to change the state. Each device’s shadow is uniquely identified by the name of the corresponding “thing”, a representation of a specific device or logical entity on the AWS Cloud. See [Managing Devices with AWS IoT](https://docs.aws.amazon.com/iot/latest/developerguide/iot-thing-management.html) for more information. More details about shadows can be found in [AWS IoT documentation](https://docs.aws.amazon.com/iot/latest/developerguide/iot-device-shadows.html). 

## Metrics

Within the MQTT Demo, Users have the ability to report Operating System, Hardware Platform and MQTT Client information to AWS IoT by sending a specially formatted string in the username field of the MQTT CONNECT packet.  

### Format

The format of the username string with metrics is:
```
<Actual_Username>?SDK=<OS_Name>&Version=<OS_Version>&Platform=<Hardware_Platform>&MQTTLib=<MQTT_Library_name>@<MQTT_Library_version>
```
where

* **Actual_Username** is the actual username used for authentication (if username and password are used for authentication).
* **OS_Name** is the Operating System the application is running on.
* **OS_Version** is the version number of the Operating System.
* **Hardware_Platform** is the Hardware Platform the application is running on.
* **MQTT_Library_name** is the MQTT Client library being used.
* **MQTT_Library_version** is the version of the MQTT Client library being used.

## Branches

### master branch
The [master](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/master) branch hosts the continuous development of the AWS IoT Embedded C SDK libraries. Please be aware that the libraries in master branch may have bugs and performance issues. Consider using the released versions of the AWS IoT Embedded C SDK for production ready software.

### v4_beta_deprecated branch
The [v4_beta_deprecated](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v4_beta_deprecated) branch contains a beta version of the AWS IoT Embedded C SDK libraries, which is now deprecated. The libraries in this branch will not be released. However, critical bugs will be fixed and tested. No new features will be added to this branch.


## Releases

All of the released versions of the AWS IoT Embedded C SDK libraries are available as git tags. For example, the latest v3 SDK version is available at [tag 3.1.0](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/v3.1.0).

## Versioning

C-SDK releases will now follow a date based versioning scheme with the format YYYYMM.NN, where: 

* Y represents the year.
* M represents the month.
* N represents the release order within the designated month (00 being the first release).
* A "major" denotation indicates the addition of new features or significant updates to multiple libraries. 

For example, a second release in June 2021 would be 202106.01. Although the SDK releases have moved to date-based versioning, each library within the SDK will still retain semantic versioning. In semantic versioning, the version number itself (X.Y.Z) indicates whether the release is a major, minor, or point release. You can use the semantic version of a library to assess the scope and impact of a new release on your application. 

## Cloning
This repo uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid git repository)

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

- A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems.

- On Linux, installation of OpenSSL development libraries and header files, *version 1.1.0 or later*, are required. The OpenSSL development libraries are usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.

  

### AWS IoT Account Setup

It is required to setup an AWS account and access the AWS IoT Console for running demos and tests. Follow the links to:

-  [Setup an AWS account](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html).

-  [Sign-in to the AWS IoT Console](https://aws.amazon.com/console/) after setting up the AWS account.


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

Generate CA key and certificate. Provide the Subject field information as appropriate.
```shell
openssl req -x509 -nodes -sha256 -days 365 -newkey rsa:2048 -keyout ca.key -out ca.crt
```

Generate server key and certificate and sign with the CA cert.
```shell

openssl req -nodes -sha256 -new -keyout server.key -out server.csr

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


#### Installing httpbin to run HTTP demos locally

1. Run httpbin through port 80:

```shell

docker pull kennethreitz/httpbin

docker run -p 80:80 kennethreitz/httpbin

```

2.  `SERVER_HOST` defined in `demos/http/http_demo_plaintext/demo_config.h` can now be set to `localhost`.

3. To run `http_demo_basic_tls`, [download ngrok](https://ngrok.com/download) in order to create an HTTPS tunnel to the httpbin server currently hosted on port 80:

```shell
./ngrok http 80 # May have to use ./ngrok.exe depending on OS or filename of the executable
```

4.  `ngrok` will provide an https link that can be substituted in `demos/http/http_demo_basic_tls/demo_config.h` and has a format of `https://ABCDEFG12345.ngrok.io`.

5. Set `SERVER_HOST` in `demos/http/http_demo_basic_tls/demo_config.h` to the https link provided by ngrok.

6. You must also download the Root CA certificate provided by ngrok and set `ROOT_CA_CERT_PATH` in `demo_config.h` to the file path of the downloaded certificate.

## Generating Documentation

The Doxygen references were created using Doxygen version 1.8.20. To generate the
Doxygen pages, please run the following commands:

```shell
cd libraries/standard/coreMQTT
doxygen docs/doxygen/config.doxyfile
cd ../../..
doxygen docs/doxygen/config.doxyfile
```

## License

This library is licensed under the [MIT License](LICENSE).
