##Overview

The AWS IoT device SDK for embedded C is a collection of C source files which can be used in embedded applications to securely connect to the [AWS IoT platform](http://docs.aws.amazon.com/iot/latest/developerguide/what-is-aws-iot.html). It includes transport clients **MQTT**, **TLS** implementations and examples for their use. It also supports AWS IoT specific features such as **Thing Shadow**. It is distributed in source form and intended to be built into customer firmware along with application code, other libraries and RTOS. For additional information about porting the Device SDK for embedded C onto additional platforms please refer to the [PortingGuide](https://github.com/aws/aws-iot-device-sdk-embedded-c/blob/master/PortingGuide.md/).

##Features
The Device SDK simplifies access to the Pub/Sub functionality of the AWS IoT broker via MQTT and provide APIs to interact with Thing Shadows. The SDK has been tested to work with the AWS IoT platform to ensure best interoperability of a device with the AWS IoT platform.

###MQTT Connection
The Device SDK provides functionality to create and maintain a mutually authenticated TLS connection over which it runs MQTT. This connection is used for any further publish operations and allow for subscribing to MQTT topics which will call a configurable callback function when these topics are received.

###Thing Shadow
The Device SDK implements the specific protocol for Thing Shadows to retrieve, update and delete Thing Shadows adhering to the protocol that is implemented to ensure correct versioning and support for client tokens. It abstracts the necessary MQTT topic subscriptions by automatically subscribing to and unsubscribing from the reserved topics as needed for each API call. Inbound state change requests are automatically signalled via a configurable callback.

## Design Goals of this SDK
The embedded C SDK was specifically designed for resource constrained devices (running on micro-controllers and RTOS).

Primary aspects are:
 * Flexibility in picking and choosing functionalities (reduce memory footprint)
 * Static memory only (no malloc’s)
 * Configurable resource usage(JSON tokens, MQTT subscription handlers, etc…)
 * Portability across RTOS due to use of wrapper functionality
 
For more information on the Architecture of the SDK refer [here](http://aws-iot-device-sdk-embedded-c-docs.s3-website-us-east-1.amazonaws.com/index.html)

##How to get started ?
Ensure you understand the AWS IoT platform and create the necessary certificates and policies. For more information on the AWS IoT platform please visit the [AWS IoT developer guide](http://docs.aws.amazon.com/iot/latest/developerguide/iot-security-identity.html).

In order to quickly get started with the AWS IoT platform, we have ported the SDK for POSIX type Operating Systems like Ubuntu, OS X and RHEL. The porting of the SDK happens at the TLS layer, and for the MQTT protocol. The SDK is configured for two TLS libraries and can be built out of the box with *GCC* using *make utility*. The tarballs can be downloaded from the below links.

* [OpenSSL](https://s3.amazonaws.com/aws-iot-device-sdk-embedded-c/linux_mqtt_openssl-1.1.0.tar)
* [mbedTLS from ARM](https://s3.amazonaws.com/aws-iot-device-sdk-embedded-c/linux_mqtt_mbedtls-1.1.0.tar)

##Installation
This section explains the individual steps to retrieve the necessary files and be able to build your first application using the AWS IoT device SDK for embedded C.

Steps:

 * Create a directory to hold your application e.g. (/home/<user>/aws_iot/my_app)
 * Change directory to this new directory
 * Download the SDK to device and place in the newly created directory
 * Expand the tarball (tar -xf <tarball.tar>).  This will create 4 directories:
 	* `aws_iot_src` - the AWS IoT SDK source files
 	* `sample_apps` - the sample applications
 	* `aws_mqtt_embedded_client_lib` - the aws MQTT client derived from [Eclipse Paho](http://www.eclipse.org/paho/clients/c/embedded/) Embedded C client
 	* `certs` - TLS certificates directory
 * Change directory to sample_apps.  The following sample applications are included:
 	* `subscribe_publish_sample` - a simple pub/sub MQTT example
 	* `shadow_sample` - a simple device shadow example using a connected window example
 	* `shadow_sample_console_echo` - a sample to work with the AWS IoT Console interactive guide
 * For each sample:
 	* Explore the example.  It connects to AWS IoT platform using MQTT and demonstrates few actions that can be performed by the SDK
 	* Build the example using make.  (''make'')
 	* Place device identity cert and private key in locations referenced in the example (certs/).  Alternatively, you can run the sample application with the ''-c'' flag to point to a specific certificate directory.
 	* Download certificate authority CA file from [Symantec](https://www.symantec.com/content/en/us/enterprise/verisign/roots/VeriSign-Class%203-Public-Primary-Certification-Authority-G5.pem) and place in location referenced in the example (certs/). Ensure the names of the cert files are the same as in the `aws_iot_config.h` file
 	* Run sample application (./subscribe_publish_sample or ./shadow_sample).  The sample will print status messages to stdout.
 	* More information on the examples could be found in the sample source file
 	
Also, for a guided example on getting started with the Thing Shadow, visit the AWS IoT Console's [Interactive Guide](https://console.aws.amazon.com/iot).

##Porting to different platforms
As Embedded devices run on different Real Time Operating Systems and TCP/IP stacks, it is one of the important design goals for the Device SDK to keep it portable. Please refer to the [porting guide](https://github.com/aws/aws-iot-device-sdk-embedded-C/blob/master/PortingGuide.md/) to get more information on how to make this SDK run on your devices (i.e. micro-controllers).

##Resources
[API Documentation](http://aws-iot-device-sdk-embedded-c-docs.s3-website-us-east-1.amazonaws.com/index.html)

[MQTT 3.1.1 Spec](http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/csprd02/mqtt-v3.1.1-csprd02.html)

##Support
If you have any technical questions about AWS IoT Device SDK, use the [AWS IoT forum](https://forums.aws.amazon.com/forum.jspa?forumID=210).
For any other questions on AWS IoT, contact [AWS Support](https://aws.amazon.com/contact-us/).

##Sample APIs
Connecting to the AWS IoT MQTT platform

```
rc = aws_iot_mqtt_connect( &connectParams ) ;
```


Subscribe to a topic

```
MQTTSubscribeParams subParams = MQTTSubscribeParamsDefault; 
subParams.mHandler = MQTTcallbackHandler;
subParams.qos = QOS_0;
subParams.pTopic = "sdkTest/sub";
rc = aws_iot_mqtt_subscribe( &subParams ) ;
```


Update Thing Shadow from a device

``` 
rc = aws_iot_shadow_update(&mqttClient,
AWS_IOT_MY_THING_NAME, 
pJsonDocumentBuffer, 
ShadowUpdateStatusCallback,
pCallbackContext, 
TIMEOUT_4SEC, 
persistenSubscription);
```