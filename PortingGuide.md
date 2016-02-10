#Porting Guide

##Scope
The scope of this document is to provide instructions to modify the provided source files and functions in of this SDK to run in a variety of embedded C–based environments (e.g. real-time OS, embedded Linux) and to be adjusted to use a specific TLS implementation as available with specific hardware platforms.

##Contents of the SDK

The SDK ported for linux can be downloaded from the below links.
 * [OpenSSL](https://s3.amazonaws.com/aws-iot-device-sdk-embedded-c/linux_mqtt_openssl-1.1.0.tar)
 * [mbedTLS from ARM](https://s3.amazonaws.com/aws-iot-device-sdk-embedded-c/linux_mqtt_mbedtls-1.1.0.tar)

The C-code files of this SDK are delivered via the following directory structure (see comment behind folder name for an explanation of its content).  

Directory structure Current SDK Directory Layout (OpenSSL)

|--`aws_iot_src` (Source files of the AWS IoT device SDK)<br> 
|--`aws_mqtt_embedded_client_lib` (MQTT library based on [Eclipse Paho](http://www.eclipse.org/paho/clients/c/embedded/) Embedded C client)<br>
|--`certs` (Private key, device certificate and Root CA) <br>
|--`docs` (Developer guide & API documentation) <br>
|--`sample_apps` (makefiles to build sample on openSSL) <br>

Current SDK Directory Layout (mbedTLS)

|--`aws_iot_src` (Source files of the AWS IoT device SDK) <br>
|--`aws_mqtt_embedded_client_lib` (MQTT library based on [Eclipse Paho](http://www.eclipse.org/paho/clients/c/embedded/) Embedded C client) <br>
|--`certs` (Private key, device certificate and Root CA) <br>
|--`docs` (Developer guide & API documentation) <br>
|--`mbedtls_lib` (mbedTLS implementation library) <br>
|--`sample_apps` (makefiles to build sample on mbedTLS) <br> 

All makefiles in this SDK were configured using the documented folder structure above, so moving or renaming folders will require modifications to makefiles.

##Explanation of folders and their content
`iot_src` : This directory contains the SDK source code including wrappers around the MQTT library, device shadow code and utilities.

`aws_mqtt_embedded_client_lib` : The source code for the Embedded C MQTT client. This client is a modified version of the [Eclipse Paho](http://www.eclipse.org/paho/clients/c/embedded/) Embedded C client. The modifications include improved keep alive handling (callback on disconnect), a fix for unsubscribe functionality, buffer protection against too large MQTT messages and additional callback context to allow for a better layered architecture of the AWS IoT SDK.

`certs` : This directory is initially empty and will need to contain the private key, the client certificate and the root CA. The client certificate and private key can be downloaded from the AWS IoT console or be created using the AWS CLI commands. The root CA can be downloaded from [Symantec](https://www.symantec.com/content/en/us/enterprise/verisign/roots/VeriSign-Class%203-Public-Primary-Certification-Authority-G5.pem).

`docs` : SDK API and file documentation.

`mbedtls_lib` : The mbedTLS source files. This directory is included when downloading the mbedTLS version of the SDK. It contains the mbedTLS source files to be built into the device application.

`sample_apps` : This directory contains sample applications as well as their makefiles. These makefiles include the relevant source files in the above two directories. The samples include a simple MQTT example which publishes and subscribes to the AWS IoT service as well as a device shadow example that shows example usage of the device shadow functionality.

##Integrating the SDK into your environment
This section explains the API calls that need to be implemented in order for the Device SDK to run on your platform. The SDK interfaces follow the driver model where only prototypes are defined by the Device SDK itself while the implementation is delegated to the user of the SDK to adjust it to the platform in use. The following sections list the needed functionality for the device SDK to run successfully on any given platform.

###Timer Functions

A timer implementation is necessary to handle request timeouts (sending MQTT connect, subscribe, etc. commands) as well as connection maintenance (MQTT keep-alive pings). Timers need millisecond resolution and are polled for expiration so these can be implemented using a "milliseconds since startup" free-running counter if desired. In the synchronous sample provided with this SDK only one command will be "in flight" at one point in time plus the client's ping timer. 

Define the `Timer` Struct as in `timer_linux.h`

`void InitTimer(Timer*);`
InitTimer - A timer structure is initialized to a clean state.

`char expired(Timer*);`
expired - a poling function to determine if the timer has expired.

`void countdown_ms(Timer*, unsigned int);`
countdown_ms - set the timer to expire in x milliseconds and start the timer.

`void countdown(Timer*, unsigned int);`
countdown - set the timer to expire in x seconds and start the timer.

`int left_ms(Timer*);`
left_ms - query time in milliseconds left on the timer.


###Network Functions

In order for the MQTT client stack to be able to communicate via the TCP/IP network protocol stack using a mutually authenticated TLS connection, the following API calls need to be implemented for your platform. 

For additional details about API parameters refer to the [API documentation](http://aws-iot-device-sdk-embedded-c-docs.s3-website-us-east-1.amazonaws.com/index.html).


`int iot_tls_init(Network *pNetwork);`
Initialize the network client / structure.  

`int iot_tls_connect(Network *pNetwork, TLSConnectParams TLSParams);`
Create a TLS TCP socket to the configure address using the credentials provided via the NewNetwork API call. This will include setting up certificate locations / arrays.


`int iot_tls_read(Network*, unsigned char*, int, int);`
Read from the TLS network buffer.

`int iot_tls_write(Network*, unsigned char*, int, int);`
Write to the TLS network buffer.

`void iot_tls_disconnect(Network *pNetwork);`
Disconnect API

`int iot_tls_destroy(Network *pNetwork);`
Clean up the connection

The TLS library generally provides the API for the underlying TCP socket.

##Time source for certificate validation
As part of the TLS handshake the device (client) needs to validate the server certificate which includes validation of the certificate lifetime requiring that the device is aware of the actual time. Devices should be equipped with a real time clock or should be able to obtain the current time via NTP. Bypassing validation of the lifetime of a certificate is not recommended as it exposes the device to a security vulnerability, as it will still accept server certificates even when they have already expired.

##Integration into operating system
###Single-Threaded implementation
The single threaded implementation implies that the sample application code (SDK + MQTT client) is called periodically by the firmware application running on the main thread. This is done by calling the function `iot_mqtt_yield` (in the simple pub-sub example) and by calling `iot_shadow_yield()` (in the device shadow example). In both cases the keep-alive time is set to 10 seconds. This means that the yield functions need to be called at a minimum frequency of once every 10 seconds. Note however that the `iot_mqtt_yield()` function takes care of reading incoming MQTT messages from the IoT service as well and hence should be called more frequently depending on the timing requirements of an application. All incoming messages can only be processed at the frequency at which `yield` is called.

###Multi-Threaded implementation
In the simple multithreaded case the yield() function can be moved to a background thread. Ensure this task runs at the frequency described above. In this case, depending on the OS mechanism, a message queue or mailbox could be used to proxy incoming MQTT messages from the callback to the worker task responsible for responding to or dispatching messages. A similar mechanism could be employed to queue publish messages from threads into a publish queue that are processed by a publishing task.

##Sample applications

The sample apps in this SDK provide a working implementation for either openSSL or mbedTLS, meaning that the function calls explained above are already implemented for these environments.

###Memory Requirements
Building the SDK shadow example using the Keil ARM toolchain on a Windows box.<br>
Target is an ARM Cortex M4.<br>
Code: ~8kb code+const<br>
RAM: ~12kb<br>
These numbers are with TLS and TCP/IP code stubbed out. This is just the SDK.

