# Demo apps for the AWS IoT Device SDK for Embedded-C

These programs demonstrate how to use the AWS IoT Device SDK for Embedded-C to
perform common AWS IoT tasks.

* [HTTP examples](#http-examples)
* [MQTT examples](#mqtt-examples)
* [Device shadow examples](#device-shadow-examples)

## HTTP examples

Example directory: `http`

### **http_demo_basic_tls**

This example resolves a domain, establishes a TCP connection, validates the
server's certificate using the root CA certificate defined in the config header,
then finally performs a TLS handshake with the HTTP server so that all
communication is encrypted. After which, HTTP Client library API is used to
send a GET, HEAD, PUT, and POST request in that order. For each request,
the HTTP response from the server (or an error code) is logged.

### **http_demo_mutual_auth**

This example resolves the AWS IoT Core endpoint, establishes a TCP connection,
performs a mutually authenticated TLS handshake occurs such that all further
communication is encrypted. After which, HTTP Client Library API is used to
make a POST request to AWS IoT Core in order to publish a message to a topic
named topic with QoS=1 so that all clients subscribed to the topic receive the
 message at least once. Any possible errors are also logged.

### **http_demo_plaintext**

This example resolves a domain, then establishes a TCP connection with an HTTP
server to demonstrate HTTP request/response communication without using an
encrypted channel (i.e. without TLS). After which, HTTP Client library API is
 used to send a GET, HEAD, PUT, and POST request in that order. For each
 request, the HTTP response from the server (or an error code) is logged.

## MQTT examples

Example directory: `mqtt`

### **mqtt_demo_basic_tls**

The example is single threaded and uses statically allocated memory;
it uses QOS2 and therefore implements a retransmission mechanism
for Publish messages. Retransmission of publish messages are attempted
when a MQTT connection is established with a session that was already
present. All the outgoing publish messages waiting to receive PUBREC
are resent in this demo. In order to support retransmission all the outgoing
publishes are stored until a PUBREC is received.

### **mqtt_demo_mutual_auth**

The example is single threaded and uses statically allocated memory;
it uses QOS1 and therefore implements a retransmission mechanism
for Publish messages. Retransmission of publish messages are attempted
when a MQTT connection is established with a session that was already
present. All the outgoing publish messages waiting to receive PUBACK
are resent in this demo. In order to support retransmission all the outgoing
publishes are stored until a PUBACK is received.

### **mqtt_demo_plaintext**

The example shown below uses MQTT APIs to send and receive MQTT packets
over the TCP connection established using POSIX sockets.
The example is single threaded and uses statically allocated memory;
it uses QOS0 and therefore does not implement any retransmission
mechanism for Publish messages. This example runs forever, if connection to
the broker goes down, the code tries to reconnect to the broker with exponential
backoff mechanism.

### **mqtt_demo_serializer**

Demo that shows use of the MQTT serializer / deserializer API
to build an ultra-light weight MQTT client. This shows that a lighter weight
MQTT client can be developed without using the higher-level
MQTT API of core_mqtt.h, but just the serializer / deserializer API.
The core_mqtt_serializer.h API lets user to serialize and
deserialize MQTT messages into a user provided buffer.
This API allows use of a statically allocated buffer.

### **mqtt_demo_subscription_manager**

Demo of an MQTT application that subscribes to multiple topic filters using a
subscription manager to manage multiple subscriptions, register different
callbacks for each subscription, and handle wildcard topics. It establishes
a TLS connection with server-only authentication, and communicates at
QoS 1 level with the broker.

## Device shadow examples

Example directory: `shadow/shadow_demo_main`

### shadow/shadow_demo_main

Demo for showing how to use the Device Shadow library's API. This version
of Device Shadow API provide macros and helper functions for assembling MQTT topics
strings, and for determining whether an incoming MQTT message is related to the
device shadow. The Device Shadow library does not depend on a MQTT library,
therefore the code for MQTT connections are placed in another file (shadow_demo_helpers.c)
to make it easy to read the code using Device Shadow library.
