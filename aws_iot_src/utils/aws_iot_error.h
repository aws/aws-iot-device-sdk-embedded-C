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


/**
 * @brief IoT Error enum
 *
 * Enumeration of return values from the IoT_* functions within the SDK.
 */
typedef enum {
	NONE_ERROR = 0,						/** Success return value - no error occurred. */
	GENERIC_ERROR = -1,					/** A generic error.  A placeholder for a more specific error. */
	NULL_VALUE_ERROR = -2,				/** A required parameter was passed as null. */
	CONNECTION_ERROR = -3,				/** A connection could not be established. */
	SUBSCRIBE_ERROR = -4,				/** The subscribe failed.  A SUBACK was not returned from the service. */
	PUBLISH_ERROR = -5,					/** The publish failed.  In the case of a QoS 1 message a PUBACK was not received. */
	DISCONNECT_ERROR = -6,				/** The disconnect failed.  The disconnect control packet could not be sent. */
	YIELD_ERROR = -7,					/** An error occurred when yielding to the IoT MQTT client.  A possible cause is an unexpected TCP socket disconnect. */
	TCP_CONNECT_ERROR = -8,				/** The TCP socket could not be established. */
	SSL_CONNECT_ERROR = -9,				/** The TLS handshake failed. */
	TCP_SETUP_ERROR =-10,				/** ? */
	SSL_CONNECT_TIMEOUT_ERROR = -11,	/** A timeout occurred while waiting for the TLS handshake to complete. */
	SSL_WRITE_ERROR = -12,				/** A Generic error based on the platform used */
	SSL_INIT_ERROR = -13,				/** ? */
	SSL_CERT_ERROR= -14,				/** An error occurred when loading the certificates.  The certificates could not be located or are incorrectly formatted. */
	UNSUBSCRIBE_ERROR = -15,			/** The unsubscribe failed.  The unsubscribe control packet could not be sent. */
	JSON_PARSE_ERROR = -16,				/** An error occurred while parsing the JSON string.  Usually malformed JSON. */
	WAIT_FOR_PUBLISH = -17,				/** Shadow: The response Ack table is currently full waiting for previously published updates */
	SSL_WRITE_TIMEOUT_ERROR = -18, 		/** SSL Write times out */
	SSL_READ_TIMEOUT_ERROR = -19, 		/** SSL Read times out */
	SSL_READ_ERROR = -20,				/** A Generic error based on the platform used */
	SHADOW_JSON_BUFFER_TRUNCATED = -21,  /** Any time an snprintf writes more than size value, this error will be returned */
	SHADOW_JSON_ERROR = -22  /** Any time an snprintf encounters an encoding error or not enough space in the given buffer */
}IoT_Error_t;

#endif /* AWS_IOT_SDK_SRC_IOT_ERROR_H_ */
