# AWS IoT Device SDK C v4.0.0 Beta 1

**[Link to API documentation](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/index.html)**

[![Build Status](https://travis-ci.org/aws/aws-iot-device-sdk-embedded-C.svg?branch=v4_beta)](https://travis-ci.org/aws/aws-iot-device-sdk-embedded-C)
[![Coverage Status](https://coveralls.io/repos/github/aws/aws-iot-device-sdk-embedded-C/badge.svg?branch=v4_beta)](https://coveralls.io/github/aws/aws-iot-device-sdk-embedded-C?branch=v4_beta)

The AWS IoT Device SDK for C is a collection of C99 source files that allow applications to securely connect to the AWS IoT platform. It includes an MQTT 3.1.1 client, as well as libraries specific to AWS IoT, such as Thing Shadows. It is distributed in source form and may be build into firmware along with application code.

This library, currently a Beta release, will supersede both the AWS IoT Device SDK Embedded C and the libraries provided with Amazon FreeRTOS.

## Building and Running Demos

This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool. **As of now, this Beta release only builds on Linux.**

### Prerequisites
- Linux system with support for POSIX threads and timers.
- CMake 3.5.0 or later.
- OpenSSL development libraries and header files, version 1.0.2g or later. This is usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.

### Build Steps
1. Register your device with AWS IoT to communicate with the AWS Cloud\.

To register your device with AWS IoT, you need the following:

- An AWS IoT policy that grants your device permissions to access AWS IoT resources\.

- An AWS IoT thing, stored on the AWS Cloud\.

- A private key and X\.509 certificate that allows your device to authenticate with AWS IoT\. 

**To create an AWS IoT policy**

    1. To create an IAM policy, you need to know your AWS Region and AWS account number\. 

       To find your AWS account number, open the [Getting Started with the AWS Management Console](https://docs.aws.amazon.com/awsconsolehelpdocs/latest/gsg/getting-started.html), locate and expand the menu beneath your account name in the upper\-right corner, and choose **My Account**\. Your account ID is displayed under **Account Settings**\.

       To find the AWS Region for your AWS account, use the AWS Command Line Interface\. To install the AWS CLI, follow the instructions in the [AWS Command Line Interface User Guide](https://docs.aws.amazon.com/cli/latest/userguide/cli-chap-install.html)\. After you install the AWS CLI, open a command prompt window and enter the following command:

       ```
       aws iot describe-endpoint
       ```

       The output should look like this:

       ```
       {
           "endpointAddress": "xxxxxxxxxxxxxx.iot.us-west-2.amazonaws.com"
       }
       ```

       In this example, the region is `us-west-2`\.

    2. Browse to the [AWS IoT console](https://console.aws.amazon.com/iotv2/)\.

    3. In the navigation pane, choose **Secure**, choose **Policies**, and then choose **Create**\.

    4. Enter a name to identify your policy\.

    5. In the **Add statements** section, choose **Advanced mode**\. Copy and paste the following JSON into the policy editor window\. Replace *aws\-region* and *aws\-account* with your AWS Region and account ID\.

       ```
       {
           "Version": "2012-10-17",
           "Statement": [
           {
               "Effect": "Allow",
               "Action": "iot:Connect",
               "Resource":"arn:aws:iot:<aws-region>:<aws-account-id>:*"
        }, 
           {
               "Effect": "Allow",
               "Action": "iot:Publish",
               "Resource": "arn:aws:iot:<aws-region>:<aws-account-id>:*"
           },
           {
                "Effect": "Allow",
                "Action": "iot:Subscribe",
                "Resource": "arn:aws:iot:<aws-region>:<aws-account-id>:*"
           },
           {
                "Effect": "Allow",
                "Action": "iot:Receive",
                "Resource": "arn:aws:iot:<aws-region>:<aws-account-id>:*"
           }
           ]
       }
       ```

    6. Choose **Create**\.

**To create an IoT thing, private key, and certificate for your device**

    1. Browse to the [AWS IoT console](https://console.aws.amazon.com/iotv2/)\.

    2. In the navigation pane, choose **Manage**, and then choose **Things**\.

    3. If you do not have any IoT things registered in your account, the **You don't have any things yet** page is displayed\. If you see this page, choose **Register a thing**\. Otherwise, choose **Create**\.

    4. On the **Creating AWS IoT things** page, choose **Create a single thing**\.

    5. On the **Add your device to the thing registry** page, enter a name for your thing, and then choose **Next**\.

    6. On the **Add a certificate for your thing** page, under **One\-click certificate creation**, choose **Create certificate**\.

    7. Download your private key and certificate by choosing the **Download** links for each\.

    8. Choose **Activate** to activate your certificate\. Certificates must be activated prior to use\.

    9. Choose **Attach a policy** to attach a policy to your certificate that grants your device access to AWS IoT operations\.

    10. Choose the policy you just created and choose **Register thing**\.

2. *Optional:* Set the following `#define` in [aws_iot_demo_config.h](demos/aws_iot_demo_config.h). You may skip this step and instead pass these configuration settings as command line options when running the demos.
    - Set `AWS_IOT_DEMO_THING_NAME` to the Thing Name you set in [step 1.2](https://docs.aws.amazon.com/iot/latest/developerguide/register-device.html). The corresponding command line option for this constant is `-i`.
    - Set `AWS_IOT_DEMO_SERVER` to your custom endpoint. This is found on the *Settings* page of the AWS IoT Console and has a format of `ABCDEFG1234567.iot.us-east-2.amazonaws.com`. The corresponding command line option for this constant is `-h`.
    - Set `AWS_IOT_DEMO_ROOT_CA` to the path of the root CA certificate downloaded in [step 1.3](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html). The corresponding command line option for this constant is `-r`.
    - Set `AWS_IOT_DEMO_CLIENT_CERT` to the path of the client certificate downloaded in [step 1.3](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html). The corresponding command line option for this constant is `-c`.
    - Set `AWS_IOT_DEMO_PRIVATE_KEY` to the path of the private downloaded in [step 1.3](https://docs.aws.amazon.com/iot/latest/developerguide/create-device-certificate.html). The corresponding command line option for this constant is `-k`.
3. Make a build directory in the SDK's root directory and `cd` into it.
    ```sh
    mkdir build
    cd build
    ```
4. Run CMake, then `make`. This builds the demo executables and places them in `build/bin`.
    ```sh
    cmake ..
    make
    ```

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
- Documentation and demo for Shadow library is incomplete.
- Auto-reconnect for MQTT connections.
- mbedTLS network stack.
- Shadow JSON document generator.
- Jobs API.
- Build support for Apple macOS.

## License

This library is licensed under the [MIT License](LICENSE).
