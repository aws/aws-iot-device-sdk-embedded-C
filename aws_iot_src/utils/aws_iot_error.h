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
 * @file aws_iot_error.h
 * @brief Definition of error types for the SDK.
 */

#ifndef AWS_IOT_SDK_SRC_IOT_ERROR_H_
#define AWS_IOT_SDK_SRC_IOT_ERROR_H_


/*! \public
 * @brief IoT Error enum
 *
 * Enumeration of return values from the IoT_* functions within the SDK.
 */
typedef enum {
	/** Return value of yield function to indicate auto-reconnect was successful */
	RECONNECT_SUCCESSFUL = 1,
	/** Success return value - no error occurred. */
	NONE_ERROR = 0,
	/** A generic error.  A placeholder for a more specific error. */
	GENERIC_ERROR = -1,
	/** A required parameter was passed as null. */
	NULL_VALUE_ERROR = -2,
	/** A connection could not be established. */
	CONNECTION_ERROR = -3,
	/** The subscribe failed.  A SUBACK was not returned from the service. */
	SUBSCRIBE_ERROR = -4,
	/** The publish failed.  In the case of a QoS 1 message a PUBACK was not received. */
	PUBLISH_ERROR = -5,
	/** The disconnect failed.  The disconnect control packet could not be sent. */
	DISCONNECT_ERROR = -6,
	/** An error occurred when yielding to the IoT MQTT client.  A possible cause is an unexpected TCP socket disconnect. */
	YIELD_ERROR = -7,
	/** The TCP socket could not be established. */
	TCP_CONNECT_ERROR = -8,
	/** The TLS handshake failed. */
	SSL_CONNECT_ERROR = -9,
	/** Error associated with setting up the parameters of a Socket */
	TCP_SETUP_ERROR =-10,
	/** A timeout occurred while waiting for the TLS handshake to complete. */
	SSL_CONNECT_TIMEOUT_ERROR = -11,
	/** A Generic write error based on the platform used */
	SSL_WRITE_ERROR = -12,
	/** SSL initialization error at the TLS layer */
	SSL_INIT_ERROR = -13,
	/** An error occurred when loading the certificates.  The certificates could not be located or are incorrectly formatted. */
	SSL_CERT_ERROR= -14,
	/** The unsubscribe failed.  The unsubscribe control packet could not be sent. */
	UNSUBSCRIBE_ERROR = -15,
	/** An error occurred while parsing the JSON string.  Usually malformed JSON. */
	JSON_PARSE_ERROR = -16,
	/** Shadow: The response Ack table is currently full waiting for previously published updates */
	WAIT_FOR_PUBLISH = -17,
	/** SSL Write times out */
	SSL_WRITE_TIMEOUT_ERROR = -18,
	/** SSL Read times out */
	SSL_READ_TIMEOUT_ERROR = -19,
	/** A Generic error based on the platform used */
	SSL_READ_ERROR = -20,
	/** Any time an snprintf writes more than size value, this error will be returned */
	SHADOW_JSON_BUFFER_TRUNCATED = -21,
	/** Any time an snprintf encounters an encoding error or not enough space in the given buffer */
	SHADOW_JSON_ERROR = -22,
	/** Returned when the Network is disconnected and reconnect is either disabled or physical layer is disconnected */
	NETWORK_DISCONNECTED = -23,
	/** Returned when the Network is disconnected and the reconnect attempt has timed out */
	NETWORK_RECONNECT_TIMED_OUT = -24,
	/** Returned when the Network is disconnected and the reconnect attempt is in progress */
	NETWORK_ATTEMPTING_RECONNECT = -25,
	/** Returned when the Network is already connected and a connection attempt is made */
	NETWORK_ALREADY_CONNECTED = -26,
	/** The MQTT RX buffer received corrupt message  */
	RX_MESSAGE_INVALID = -27,
	/** The MQTT RX buffer received a bigger message. The message will be dropped  */
	RX_MESSAGE_BIGGER_THAN_MQTT_RX_BUF = -28
}IoT_Error_t;

#endif /* AWS_IOT_SDK_SRC_IOT_ERROR_H_ */
