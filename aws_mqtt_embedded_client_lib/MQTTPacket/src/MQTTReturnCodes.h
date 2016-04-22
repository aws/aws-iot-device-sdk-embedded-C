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
 * @file MQTTErrorCodes.h
 * @brief Definition of error types for the MQTT Client
 */

#ifndef __MQTT_ERRORCODES_H
#define __MQTT_ERRORCODES_H

/* all failure return codes must be negative */
typedef enum {
    MQTT_NETWORK_MANUALLY_DISCONNECTED = 5,
    MQTT_CONNACK_CONNECTION_ACCEPTED = 4,
    MQTT_ATTEMPTING_RECONNECT = 3,
    MQTT_NOTHING_TO_READ = 2,
    MQTT_NETWORK_RECONNECTED = 1,
    SUCCESS = 0,
    FAILURE = -1,
    BUFFER_OVERFLOW = -2,
    MQTT_UNKNOWN_ERROR = -3,
    MQTT_NETWORK_DISCONNECTED_ERROR = -4,
    MQTT_NETWORK_ALREADY_CONNECTED_ERROR = -5,
    MQTT_NULL_VALUE_ERROR = -6,
    MQTT_MAX_SUBSCRIPTIONS_REACHED_ERROR = -7,
    MQTT_RECONNECT_TIMED_OUT = -8,
    MQTTPACKET_BUFFER_TOO_SHORT = -9,
    MQTTPACKET_READ_ERROR = -10,
    MQTTPACKET_READ_COMPLETE = -11,
    MQTT_CONNACK_UNKNOWN_ERROR = -12,
    MQTT_CONANCK_UNACCEPTABLE_PROTOCOL_VERSION_ERROR = -13,
    MQTT_CONNACK_IDENTIFIER_REJECTED_ERROR = -14,
    MQTT_CONNACK_SERVER_UNAVAILABLE_ERROR = -15,
    MQTT_CONNACK_BAD_USERDATA_ERROR = -16,
    MQTT_CONNACK_NOT_AUTHORIZED_ERROR = -17,
	MQTT_BUFFER_RX_MESSAGE_INVALID = -18
}MQTTReturnCode;

#endif //__MQTT_ERRORCODES_H
