/*
 * Copyright 2010-2015 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/**
 * @file aws_iot_mqtt_interface.h
 * @brief Interface definition for MQTT client.
 */

#ifndef AWS_IOT_SDK_SRC_IOT_MQTT_INTERFACE_H_
#define AWS_IOT_SDK_SRC_IOT_MQTT_INTERFACE_H_

#include "stddef.h"
#include "stdbool.h"
#include "stdint.h"
#include "aws_iot_error.h"

/**
 * @brief MQTT Version Type
 *
 * Defining an MQTT version type.
 *
 */
typedef enum {
	MQTT_3_1 = 3,	///< MQTT 3.1   (protocol message byte = 3)
	MQTT_3_1_1 = 4	///< MQTT 3.1.1 (protocol message byte = 4)
} MQTT_Ver_t;

/**
 * @brief Quality of Service Type
 *
 * Defining a QoS type.
 * @note QoS 2 is \b NOT supported by the AWS IoT Service at the time of this SDK release.
 *
 */
typedef enum {
	QOS_0,	///< QoS 0 = at most once delivery
	QOS_1,	///< QoS 1 = at least once delivery
	QOS_2	///< QoS 2 is NOT supported
} QoSLevel;

/**
 * @brief Last Will and Testament Definition
 *
 * Defining a type for LWT parameters.
 * @note Retained messages are \b NOT supported by the AWS IoT Service at the time of this SDK release.
 *
 */
typedef struct {
	const char *pTopicName;	///< LWT Topic
	const char *pMessage;	///< Message to be delivered as LWT
	bool isRetained;		///< NOT supported
	QoSLevel qos;			///< QoS of LWT message
} MQTTwillOptions;
extern const MQTTwillOptions MQTTwillOptionsDefault;

/**
 * @brief Disconnect Callback Handler Type
 *
 * Defining a TYPE for definition of disconnect callback function pointers.
 *
 */
typedef void (*iot_disconnect_handler)(void);

/**
 * @brief MQTT Connection Parameters
 *
 * Defining a type for MQTT connection parameters.  Passed into client when establishing a connection.
 *
 */
typedef struct {
	uint8_t enableAutoReconnect;		///< Set to true to enable auto reconnect
	char *pHostURL;						///< Pointer to a string defining the endpoint for the MQTT service
	uint16_t port;						///< MQTT service listening port
	char *pRootCALocation;				///< Pointer to a string defining the Root CA file (full file, not path)
	char *pDeviceCertLocation;			///< Pointer to a string defining the device identity certificate file (full file, not path)
	char *pDevicePrivateKeyLocation;	///< Pointer to a string defining the device private key file (full file, not path)
	char *pClientID;					///< Pointer to a string defining the MQTT client ID (this needs to be unique \b per \b device across your AWS account)
	char *pUserName;					///< Not used in the AWS IoT Service
	char *pPassword;					///< Not used in the AWS IoT Service
	MQTT_Ver_t MQTTVersion;				///< Desired MQTT version used during connection
	uint16_t KeepAliveInterval_sec;		///< MQTT keep alive interval in seconds.  Defines inactivity time allowed before determining the connection has been lost.
	bool isCleansession;				///< MQTT clean session.  True = this session is to be treated as clean.  Previous server state is cleared and no stated is retained from this connection.
	bool isWillMsgPresent;				///< Is there a LWT associated with this connection?
	MQTTwillOptions will;				///< MQTT LWT parameters.
	uint32_t mqttCommandTimeout_ms;		///< Timeout for MQTT blocking calls.  In milliseconds.
	uint32_t tlsHandshakeTimeout_ms;	///< TLS handshake timeout.  In milliseconds.
	bool isSSLHostnameVerify;			///< Client should perform server certificate hostname validation.
	iot_disconnect_handler disconnectHandler;	///< Callback to be invoked upon connection loss.
} MQTTConnectParams;
extern const MQTTConnectParams MQTTConnectParamsDefault;

/**
 * @brief MQTT Message Parameters
 *
 * Defines a type for properties of MQTT messages including topic, payload an QoS.
 *
 */
typedef struct {
	QoSLevel qos;			///< Message Quality of Service
	bool isRetained;		///< Retained messages are \b NOT supported by the AWS IoT Service at the time of this SDK release.
	bool isDuplicate;		///< Is this message a duplicate QoS > 0 message?  Handled automatically by the MQTT client.
	uint16_t id;			///< Message sequence identifier.  Handled automatically by the MQTT client.
	void *pPayload;			///< Pointer to MQTT message payload (bytes).
	uint32_t PayloadLen;	///< Length of MQTT payload.
} MQTTMessageParams;
extern const MQTTMessageParams MQTTMessageParamsDefault;
/**
 * @brief MQTT Callback Function Parameters
 *
 * Defines a type for parameters returned to the user upon receipt of a publish message on a subscribed topic.
 *
 */
typedef struct {
	char *pTopicName;					///< Pointer to the topic string on which the message was delivered.  In the case of a wildcard subscription this is the actual topic, not the wildcard filter.
	uint16_t TopicNameLen;				///< Length of the topic string.
	MQTTMessageParams MessageParams;	///< Message parameters structure.
} MQTTCallbackParams;
extern const MQTTCallbackParams MQTTCallbackParamsDefault;

/**
 * @brief MQTT Callback Function
 *
 * Defines a type for the function pointer which stores the message callback function.
 * A pointer to the desired callback function to be invoked upon receipt of a message on a subscribed toipc.
 * Supplied upon subscribing to a topic.
 *
 */
typedef int32_t (*iot_message_handler)(MQTTCallbackParams params);

/**
 * @brief MQTT Subscription Parameters
 *
 * Defines the parameters needed when subscribing to an MQTT topic.
 *
 */
typedef struct {
	char *pTopic;					///< Pointer to the string defining the desired subscription topic.
	QoSLevel qos;					///< Quality of service of the subscription.
	iot_message_handler mHandler;	///< Callback to be invoked upon receipt of a message on the subscribed topic.
} MQTTSubscribeParams;
extern const MQTTSubscribeParams MQTTSubscribeParamsDefault;

/**
 * @brief MQTT Publish Parameters
 *
 * Defines a type for parameters supplied when publishing an MQTT message.
 *
 */
typedef struct {
	char *pTopic;						///< Pointer to the string defining the desired publishing topic.
	MQTTMessageParams MessageParams;	///< Parameters defining the message to be published.
} MQTTPublishParams;
extern const MQTTPublishParams MQTTPublishParamsDefault;

/**
 * @brief MQTT Connection Function
 *
 * Called to establish an MQTT connection with the AWS IoT Service
 *
 * @param pParams	Pointer to MQTT connection parameters
 * @return An IoT Error Type defining successful/failed connection
 */
IoT_Error_t aws_iot_mqtt_connect(MQTTConnectParams *pParams);

/**
 * @brief Publish an MQTT message on a topic
 *
 * Called to publish an MQTT message on a topic.
 * @note Call is blocking.  In the case of a QoS 0 message the function returns
 * after the message was successfully passed to the TLS layer.  In the case of QoS 1
 * the function returns after the receipt of the PUBACK control packet.
 *
 * @param pParams	Pointer to MQTT publish parameters
 * @return An IoT Error Type defining successful/failed publish
 */
IoT_Error_t aws_iot_mqtt_publish(MQTTPublishParams *pParams);

/**
 * @brief Subscribe to an MQTT topic.
 *
 * Called to send a subscribe message to the broker requesting a subscription
 * to an MQTT topic.
 * @note Call is blocking.  The call returns after the receipt of the SUBACK control packet.
 *
 * @param pParams	Pointer to MQTT subscribe parameters
 * @return An IoT Error Type defining successful/failed subscription
 */
IoT_Error_t aws_iot_mqtt_subscribe(MQTTSubscribeParams *pParams);

/**
 * @brief Unsubscribe to an MQTT topic.
 *
 * Called to send an usubscribe message to the broker requesting removal of a subscription
 * to an MQTT topic.
 * @note Call is blocking.  The call returns after the receipt of the UNSUBACK control packet.
 *
 * @param pTopic Pointer to the requested topic string. Ensure the string is null terminated
 * @return An IoT Error Type defining successful/failed unsubscription
 */
IoT_Error_t aws_iot_mqtt_unsubscribe(char *pTopic);

/**
 * @brief MQTT Manual Re-Connection Function
 *
 * Called to establish an MQTT connection with the AWS IoT Service
 * using parameters from the last time a connection was attempted
 * Use after disconnect to start the reconnect process manually
 * Makes only one reconnect attempt
 *
 * @return An IoT Error Type defining successful/failed connection
 */
IoT_Error_t aws_iot_mqtt_attempt_reconnect(void);

/**
 * @brief Disconnect an MQTT Connection
 *
 * Called to send a disconnect message to the broker.
 *
 * @return An IoT Error Type defining successful/failed send of the disconnect control packet.
 */
IoT_Error_t aws_iot_mqtt_disconnect(void);

/**
 * @brief Yield to the MQTT client
 *
 * Called to yield the current thread to the underlying MQTT client.  This time is used by
 * the MQTT client to manage PING requests to monitor the health of the TCP connection as
 * well as periodically check the socket receive buffer for subscribe messages.  Yield()
 * must be called at a rate faster than the keepalive interval.  It must also be called
 * at a rate faster than the incoming message rate as this is the only way the client receives
 * processing time to manage incoming messages.
 *
 * @param timeout Maximum number of milliseconds to pass thread execution to the client.
 * @return An IoT Error Type defining successful/failed client processing.
 *         If this call results in an error it is likely the MQTT connection has dropped.
 *         iot_is_mqtt_connected can be called to confirm.
 */
IoT_Error_t aws_iot_mqtt_yield(int timeout);

/**
 * @brief Is the MQTT client currently connected?
 *
 * Called to determine if the MQTT client is currently connected.  Used to support logic
 * in the device application around reconnecting and managing offline state.
 *
 * @return true = connected, false = not currently connected
 */
bool aws_iot_is_mqtt_connected(void);

/**
 * @brief Is the MQTT client set to reconnect automatically?
 *
 * Called to determine if the MQTT client is set to reconnect automatically.
 * Used to support logic in the device application around reconnecting
 *
 * @return true = enabled, false = disabled
 */
bool aws_iot_is_autoreconnect_enabled(void);

/**
 * @brief Enable or Disable AutoReconnect on Network Disconnect
 *
 * Called to enable or disabled the auto reconnect features provided with the SDK
 *
 * @param value set to true for enabling and false for disabling
 *
 * @return IoT_Error_t Type defining successful/failed API call
 */
IoT_Error_t aws_iot_mqtt_autoreconnect_set_status(bool value);

typedef IoT_Error_t (*pConnectFunc_t)(MQTTConnectParams *pParams);
typedef IoT_Error_t (*pPublishFunc_t)(MQTTPublishParams *pParams);
typedef IoT_Error_t (*pSubscribeFunc_t)(MQTTSubscribeParams *pParams);
typedef IoT_Error_t (*pUnsubscribeFunc_t)(char *pTopic);
typedef IoT_Error_t (*pDisconnectFunc_t)(void);
typedef IoT_Error_t (*pYieldFunc_t)(int timeout);
typedef bool (*pIsConnectedFunc_t)(void);
typedef bool (*pIsAutoReconnectEnabledFunc_t)(void);
typedef IoT_Error_t (*pReconnectFunc_t)();
typedef IoT_Error_t (*pSetAutoReconnectStatusFunc_t)(bool);
/**
 * @brief MQTT Client Type Definition
 *
 * Defines a structure of function pointers, each implementing a corresponding iot_mqtt_*
 * function.  In this way any MQTT client which implements the iot_mqtt_* interface
 * can be swapped in under the MQTT/Shadow layer.
 *
 */
typedef struct{
	pConnectFunc_t connect;				///< function implementing the iot_mqtt_connect function
	pPublishFunc_t publish;				///< function implementing the iot_mqtt_publish function
	pSubscribeFunc_t subscribe;			///< function implementing the iot_mqtt_subscribe function
	pUnsubscribeFunc_t unsubscribe;		///< function implementing the iot_mqtt_unsubscribe function
	pDisconnectFunc_t disconnect;		///< function implementing the iot_mqtt_disconnect function
	pYieldFunc_t yield;					///< function implementing the iot_mqtt_yield function
	pIsConnectedFunc_t isConnected;		///< function implementing the iot_is_mqtt_connected function
	pReconnectFunc_t reconnect;			///< function implementing the iot_mqtt_reconnect function
	pIsAutoReconnectEnabledFunc_t isAutoReconnectEnabled;	///< function implementing the iot_is_autoreconnect_enabled function
	pSetAutoReconnectStatusFunc_t setAutoReconnectStatus;	///< function implementing the iot_mqtt_autoreconnect_set_status function
}MQTTClient_t;


/**
 * @brief Set the MQTT client
 *
 * This function provides a way to pass in an MQTT client implementation to the
 * AWS IoT MQTT wrapper layer.  This is done through function pointers to the
 * interface functions.
 *
 */
void aws_iot_mqtt_init(MQTTClient_t *pClient);


#endif /* AWS_IOT_SDK_SRC_IOT_MQTT_INTERFACE_H_ */
