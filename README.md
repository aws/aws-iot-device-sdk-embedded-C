#AWS IoT Embedded-C SDK

##What is Embedded-C SDK ?

It is a collection of C source files which can be used in embedded applications when connecting and using the [AWS IoT service](http://docs.aws.amazon.com/iot/latest/developerguide/what-is-aws-iot.html). It will include transport clients **(MQTT)**, **TLS** implementations and examples on their use. It also includes AWS IoT specific features such as **Thing Shadow**. It is distributed in source form and intended to be built into customer firmware along with application code, other libraries and RTOS. 


##Why Do I Need the SDK?
Strictly speaking the SDK is not required to connect to and use the AWS IoT Service. The service will accept a TLS client authenticated MQTT connection from any client.  However it is the goal of this SDK significantly streamline this task for device developers.  As mentioned above it will also include functionality specific to the AWS IoT Service. The SDK will be optimized to work with AWS IoT service to save resource and setup time.

## Design Goals of this SDK
Embedded C SDK is for resource constrained devices (running on micro-controllers and RTOS).

Primary Quality Attributes of this SDK are
 * Flexibility in picking and choosing functionalities
 * Static memory only (no malloc’s)
 * Configurable resource usage(JSON tokens, MQTT subscription handlers, etc…)
 * Portability across RTOS
 
For more information on the Architecture of the SDK refer [here](http://aws-iot-device-sdk-embedded-c-docs.s3-website-us-east-1.amazonaws.com/index.html)

##How to get started ?
Ensure you understand the AWS IoT service and create the necessary certificates and policies. For more information on the AWS IoT Service please visit [this](https://aws.amazon.com/iot)

This repository is for our source files, but in order to quickly get started with the AWS IoT service, we have ported the SDK for POSIX type Operating Systems like Ubuntu, OS X and RHEL. The porting of the SDK happens at the TLS layer, underneath the MQTT protocol. The SDK is configured for two TLS libraries and can be built out of the box with *GCC* using *make utility*. The tarballs can be downloaded from the below links.

* [OpenSSL](https://s3.amazonaws.com/aws-iot-device-sdk-embedded-c/linux_mqtt_openssl-1.0.0.tar)
* [mbedTLS from ARM](https://s3.amazonaws.com/aws-iot-device-sdk-embedded-c/linux_mqtt_mbedtls-1.0.0.tar)

Steps:

 * Create a directory to hold your application e.g. (/home/<user>/aws_iot/my_app)
 * Change directory to this new directory
 * Download the SDK to device and place in the newly created directory
 * Expand the tarball (tar -xf <tarball.tar>).  This will create 4 directories:
 	* `aws_iot_src` - the AWS IoT SDK source files
 	* `sample_apps` - the sample applications
 	* `aws_mqtt_embedded_client_lib` - the aws MQTT client derived from Paho Embedded C client
 	* `certs` - TLS certificates directory
 * Change directory to sample_apps.  The following sample applications are included:
 	* `subscribe_publish_sample` - a simple pub/sub MQTT example
 	* `shadow_sample` - a simple device shadow example using a connected window example
 	* `shadow_sample_console_echo` - a sample to work with the AWS IoT Console interactive guide
 * For each sample:
 	* Explore the example.  It connects to AWS IoT Service using MQTT and demonstrates few actions that can be performed by the SDK
 	* Build the example using make.  (''make'')
 	* Place device identity cert and private key in locations referenced in the example (certs/).  Alternatively, you can run the sample application with the ''-c'' flag to point to a specific certificate directory.
 	* Download certificate authority CA file from this [link](https://www.symantec.com/content/en/us/enterprise/verisign/roots/VeriSign-Class%203-Public-Primary-Certification-Authority-G5.pem) and place in location referenced in the example (certs/). Ensure the names of the cert files are the same as in the `aws_iot_config.h` file
 	* Run sample application (./subscribe_publish_sample or ./shadow_sample).  The sample will print status messages to stdout.
 	* More information on the examples could be found in the sample source file
 	
Also, for a guided example on getting started with the Thing Shadow, visit the AWS IoT Console's [Interactive Guide](https://console.aws.amazon.com/iot).
##Further Steps - Porting
As Embedded device run on different Real Time Operating Systems and IP stack, it is one of the important design goals for us to keep the SDK portable. Please find the [porting guide](http://aws-iot-device-sdk-embedded-c-docs.s3-website-us-east-1.amazonaws.com/index.html) to get more information on how to make this SDK run on your devices(micro-controllers).

##Resources
[API Documentation](http://aws-iot-device-sdk-embedded-c-docs.s3-website-us-east-1.amazonaws.com/index.html)

[MQTT 3.1.1 Spec](http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/csprd02/mqtt-v3.1.1-csprd02.html)

##Support
If you have any technical questions about AWS IoT Device SDK, use the [AWS IoT forum](https://forums.aws.amazon.com/forum.jspa?forumID=30).

For any other questions on AWS IoT, contact [AWS Support](https://aws.amazon.com/contact-us/).


##Sample APIs
Connecting to the AWS IoT MQTT Service
``` rc = aws_iot_mqtt_connect(&connectParams);```

Subscribe to a topic

```
MQTTSubscribeParams subParams = MQTTSubscribeParamsDefault; 
subParams.mHandler = MQTTcallbackHandler;
subParams.qos = QOS_0;
subParams.pTopic = "sdkTest/sub";
rc = aws_iot_mqtt_subscribe(&subParams);
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
