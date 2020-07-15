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
 * @file MQTT_SerializePublish_harness.c
 * @brief Implements the proof harness for MQTT_SerializePublish function.
 */
#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTPublishInfo_t * pPublishInfo;
    uint16_t packetId;
    size_t remainingLength;
    size_t packetSize;
    const MQTTFixedBuffer_t * pFixedBuffer;
    MQTTStatus_t status = MQTTSuccess;

    pPublishInfo = allocateMqttPublishInfo( NULL );
    __CPROVER_assume( isValidMqttPublishInfo( pPublishInfo ) );

    pFixedBuffer = allocateMqttFixedBuffer( NULL );
    __CPROVER_assume( isValidMqttFixedBuffer( pFixedBuffer ) );

    /* Before calling MQTT_SerializePublish() it is up to the application to
     * make sure that the information in MQTTPublishInfo_t can fit into the
     * MQTTFixedBuffer_t. It is a violation of the API to call
     * MQTT_SerializePublish() without first calling MQTT_GetPublishPacketSize(). */
    if( pPublishInfo != NULL )
    {
        /* The output parameter pPacketSize of the function MQTT_GetConnectPacketSize()
         * must not be NULL. packetSize returned is not used in this proof, but 
         * is used normally by the application to verify the size of their 
         * MQTTFixedBuffer_t. MQTT_SerializeConnect() will use the remainingLength 
         * to recalculate the packetSize. */
        status = MQTT_GetPublishPacketSize( pPublishInfo, &remainingLength, &packetSize );
    }

    if( status == MQTTSuccess )
    {
        /* For coverage it is expected that a NULL pPublishInfo could
         * reach this function. */
        MQTT_SerializePublish( pPublishInfo,
                               packetId,
                               remainingLength,
                               pFixedBuffer );
    }
}
