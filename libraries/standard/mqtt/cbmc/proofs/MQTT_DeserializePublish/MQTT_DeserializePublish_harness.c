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

/**
 * @file MQTT_DeserializePublish_harness.c
 * @brief Implements the proof harness for MQTT_DeserializePublish function.
 */

#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTPacketInfo_t * pIncomingPacket;
    MQTTPublishInfo_t * pPublishInfo;
    uint16_t packetId;

    pIncomingPacket = allocateMqttPacketInfo( pIncomingPacket );
    __CPROVER_assume( isValidMqttPacketInfo( pIncomingPacket ) );

    pPublishInfo = allocateMqttPublishInfo( pPublishInfo );
    __CPROVER_assume( isValidMqttPublishInfo( pPublishInfo ) );

    /* This function grabs the topic name, the topic name length, the
     * the payload, and the payload length. */
    MQTT_DeserializePublish( pIncomingPacket, packetId, pPublishInfo );
}
