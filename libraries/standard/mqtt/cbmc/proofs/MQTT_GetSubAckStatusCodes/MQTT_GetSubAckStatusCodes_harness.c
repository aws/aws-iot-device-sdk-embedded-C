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
 * @file MQTT_GetSubAckStatusCodes_harness.c
 * @brief Implements the proof harness for MQTT_GetSubAckStatusCodes function.
 */

#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTPacketInfo_t * pSubackPacket;
    uint8_t ** pPayloadStart;
    size_t * pPayloadSize;

    pSubackPacket = allocateMqttPacketInfo( NULL );
    __CPROVER_assume( isValidMqttPacketInfo( pSubackPacket ) );

    /* pPayloadStart and pPayloadSize are output parameters, and
     * thus, don't carry any assumptions. */
    pPayloadStart = mallocCanFail( sizeof( uint8_t * ) );
    pPayloadSize = mallocCanFail( sizeof( size_t ) );

    MQTT_GetSubAckStatusCodes( pSubackPacket,
                               pPayloadStart,
                               pPayloadSize );
}
