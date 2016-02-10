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
 * @file MQTTMessage.h
 * @brief Definition of Messages for the MQTT Client
 */

#ifndef __MQTT_MESSAGE_H
#define __MQTT_MESSAGE_H

/* Enum order should match the packet ids array defined in MQTTFormat.c */
typedef enum msgTypes {
    UNKNOWN = -1,
    CONNECT = 1,
    CONNACK = 2,
    PUBLISH = 3,
    PUBACK = 4,
    PUBREC = 5,
    PUBREL = 6,
    PUBCOMP = 7,
    SUBSCRIBE = 8,
    SUBACK = 9,
    UNSUBSCRIBE = 10,
    UNSUBACK = 11,
    PINGREQ = 12,
    PINGRESP = 13,
    DISCONNECT = 14
}MessageTypes;

typedef enum QoS {
    QOS0 = 0,
    QOS1 = 1,
    QOS2 = 2
}QoS;

typedef struct {
    QoS qos;
    uint8_t retained;
    uint8_t dup;
    uint16_t id;
    void *payload;
    size_t payloadlen;
}MQTTMessage;

#endif //__MQTT_MESSAGE_H
