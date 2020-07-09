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
 * @file MQTT_SerializeSubscribe_harness.c
 * @brief Implements the proof harness for MQTT_SerializeSubscribe function.
 */
#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTSubscribeInfo_t * pSubscriptionList = NULL;
    size_t subscriptionCount;
    size_t remainingLength = 0;
    uint16_t packetId;
    size_t packetSize = 0;
    MQTTFixedBuffer_t * pFixedBuffer = NULL;
    MQTTStatus_t status = MQTTSuccess;

    __CPROVER_assume( subscriptionCount < SUBSCRIPTION_COUNT_MAX );

    pSubscriptionList = allocateMqttSubscriptionList( pSubscriptionList, subscriptionCount );
    __CPROVER_assume( isValidMqttSubscriptionList( pSubscriptionList, subscriptionCount ) );

    pFixedBuffer = allocateMqttFixedBuffer( pFixedBuffer );
    __CPROVER_assume( isValidMqttFixedBuffer( pFixedBuffer ) );

    if( pSubscriptionList != NULL )
    {
        status = MQTT_GetSubscribePacketSize( pSubscriptionList,
                                              subscriptionCount,
                                              &remainingLength,
                                              &packetSize );
    }

    if( status == MQTTSuccess )
    {
        MQTT_SerializeSubscribe( pSubscriptionList,
                                 subscriptionCount,
                                 packetId,
                                 remainingLength,
                                 pFixedBuffer );
    }
}
