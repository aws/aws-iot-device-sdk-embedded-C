/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#ifndef MQTT_STATE_H
#define MQTT_STATE_H

#include "mqtt.h"

typedef enum MQTTStateOperation
{
    MQTT_SEND,
    MQTT_RECEIVE,
} MQTTStateOperation_t;

MQTTPublishState_t MQTT_ReserveState( MQTTContext_t * pMqttContext,
                                      uint16_t packetId,
                                      MQTTQoS_t qos );

MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos );

MQTTPublishState_t MQTT_UpdateStatePublish( MQTTContext_t * pMqttContext,
                                            uint16_t packetId,
                                            MQTTStateOperation_t opType,
                                            MQTTQoS_t receivedQos );

MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos );

MQTTPublishState_t MQTT_UpdateStateAck( MQTTContext_t * pMqttContext,
                                        uint16_t packetId,
                                        MQTTPubAckType_t packetType,
                                        MQTTStateOperation_t opType );

uint16_t MQTT_StateSelect( MQTTContext_t * pMqttContext,
                           MQTTPublishState_t searchState );

#endif /* ifndef MQTT_STATE_H */
