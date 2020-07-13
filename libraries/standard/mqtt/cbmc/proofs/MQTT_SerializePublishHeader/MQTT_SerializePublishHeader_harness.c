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
 * @file MQTT_SerializePublishHeader_harness.c
 * @brief Implements the proof harness for MQTT_SerializePublishHeader function.
 */
#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTPublishInfo_t * pPublishInfo;
    uint16_t packetId;
    size_t remainingLength;
    size_t packetSize;
    MQTTFixedBuffer_t * pFixedBuffer;
    size_t * pHeaderSize;
    MQTTStatus_t status = MQTTSuccess;

    pPublishInfo = allocateMqttPublishInfo( pPublishInfo );
    __CPROVER_assume( isValidMqttPublishInfo( pPublishInfo ) );

    pFixedBuffer = allocateMqttFixedBuffer( pFixedBuffer );
    __CPROVER_assume( isValidMqttFixedBuffer( pFixedBuffer ) );

    /* Allocate space for a returned header size to get coverage of a possibly
     * NULL input. */
    pHeaderSize = mallocCanFail( sizeof( size_t ) );

    /* Before calling MQTT_SerializePublishHeader() it is up to the application
     * to verify that the information in MQTTPublishInfo_t can fit into the
     * MQTTFixedBuffer_t. It is a violation of the API to call
     * MQTT_SerializePublishHeader() without first calling MQTT_GetPublishPacketSize(). */
    if( pPublishInfo != NULL )
    {
        /* packetSize must be non-NULL in order for the verification to proceed.
         * The packetSize returned is not used in this proof, but is used normally
         * by the application to verify the size of their MQTTFixedBuffer_t.
         * MQTT_SerializePublishHeader() will use the remainingLength to
         * recalculate the packetSize. */
        status = MQTT_GetPublishPacketSize( pPublishInfo,
                                            &remainingLength,
                                            &packetSize );
    }

    if( status == MQTTSuccess )
    {
        /* For coverage it is expected that a NULL pPublishInfo could
         * reach this function. */
        MQTT_SerializePublishHeader( pPublishInfo,
                                     packetId,
                                     remainingLength,
                                     pFixedBuffer,
                                     pHeaderSize );
    }
}
