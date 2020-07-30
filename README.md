
# AWS IoT Device SDK C v4.0.2

  

## Development branch

This branch currently hosts development of AWS IoT Embedded C SDK version 4 beta 2. It is currently a work in progress and should not be used to create any products at the moment. We will update this README when that status changes.

  

## Building and Running Demos

  

This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool.

  

### Prerequisites

- CMake 3.13.0 or later and a C90 compiler.

- A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems.

- On Linux systems, installation of OpenSSL development libraries and header files, *version 1.1.0 or later*, are required. The OpenSSL development libraries are usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.

  

### AWS IoT Account Setup

It is required to setup an AWS account and access the AWS IoT Console for running demos and tests. Follow the links to:

-  [Setup an AWS account](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html).

-  [Sign-in to the AWS IoT Console](https://docs.aws.amazon.com/iot/latest/developerguide/iot-console-signin.html) after setting up the AWS account.

  

*Note: If using the Provisioning library, a fleet provisioning template, a provisioning claim, IoT policies and IAM policies need to be setup for the AWS account. Complete the steps to setup your device and AWS IoT account outlined [here](https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html#use-claim).*

  

### Configuring the mutual auth demos

- You can pass the following configuration settings as command line options in order to run the mutual auth demos: `cmake .. -DAWS_IOT_ENDPOINT="aws-iot-endpoint" -DCLIENT_CERT_PATH="certificate-path" -DCLIENT_PRIVATE_KEY_PATH="private-key-path"`

- In order to set these settings manually, edit `demo_config.h` in `demos/mqtt/mqtt_demo_mutual_auth/` and `demos/http/http_demo_mutual_auth/` to `#define` the following:

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

## Installing Mosquitto to run MQTT demos locally

1.  Download the official Docker image for Mosquitto.

```shell

docker pull eclipse-mosquitto:latest

```
1.  `BROKER_ENDPOINT` defined in `demos/mqtt/mqtt_demo_basic_tls/demo_config.h` can now be set to `localhost`.

1. For TLS communication with Mosquitto broker, server and CA credentials need to be created. Use OpenSSL commands to generate the credentials for the Mosquitto server.

Generating CA key and certificate. Provide the Subject field information as appropriate.
```shell

openssl req -x509 -nodes -sha256 -days 365 -newkey rsa:2048 -keyout ca.key -out ca.crt

```

Generating server key and certificate by getting it signed by the CA cert.
```shell

openssl req -nodes -sha256 -new -keyout server.key -out server.csr
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

```shell

docker run -it -p 8883:8883 -v $(pwd):/mosquitto/config/ --name mosquitto-basic-tls eclipse-mosquitto:latest

```

1. Set `ROOT_CA_CERT_PATH` to the server certificate used when setting up TLS authentication for your local Mosquitto server.

  

## Optional: Installing httpbin to run HTTP demos locally

1. Run httpbin through port 80:

```shell

docker pull kennethreitz/httpbin

docker run -p 80:80 kennethreitz/httpbin

```

1.  `SERVER_HOST` defined in `demos/http/http_demo_plaintext/demo_config.h` can now be set to `localhost`.

1. To run `http_demo_basic_tls`, [download ngrok](https://ngrok.com/download) in order to create an HTTPS tunnel to the httpbin server currently hosted on port 80:

```shell

./ngrok http 80 # May have to use ./ngrok.exe depending on OS or filename of the executable

```

1.  `ngrok` will provide an https link that can be substituted in `demos/http/http_demo_basic_tls/demo_config.h` and has a format of `https://ABCDEFG12345.ngrok.io`.

1. Set `SERVER_HOST` in `demos/http/http_demo_basic_tls/demo_config.h` to the https link provided by ngrok.

1. You must also download the Root CA certificate provided by ngrok and set `ROOT_CA_CERT_PATH` in `demo_config.h` to the file path of the downloaded certificate.
