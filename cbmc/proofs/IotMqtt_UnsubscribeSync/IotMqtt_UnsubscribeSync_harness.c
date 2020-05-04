/*
 * IoT MQTT V2.1.0
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/**
 * @file IotMqtt_UnsubscribeSync_harness.c
 * @brief Implements the proof harness for IotMqtt_UnsubscribeSync function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

void harness()
{
    size_t subscriptionCount;

    __CPROVER_assume( subscriptionCount < SUBSCRIPTION_COUNT_MAX );

    IotMqttSubscription_t * subscriptionList =
        allocate_IotMqttSubscriptionArray( NULL, subscriptionCount );
    __CPROVER_assume( valid_IotMqttSubscriptionArray( subscriptionList,
                                                      subscriptionCount ) );

    IotMqttConnection_t mqttConnection = allocate_IotMqttConnection( NULL );
    __CPROVER_assume( mqttConnection != NULL );
    ensure_IotMqttConnection_has_lists( mqttConnection );
    __CPROVER_assume( valid_IotMqttConnection( mqttConnection ) );
    __CPROVER_assume( IS_STUBBED_NETWORKIF_SEND( mqttConnection->
                                                    pNetworkInterface ) );
    __CPROVER_assume( IS_STUBBED_NETWORKIF_DESTROY( mqttConnection->
                                                       pNetworkInterface ) );

    uint32_t flags;
    uint32_t timeoutMs;

    IotMqtt_UnsubscribeSync( mqttConnection,
                             subscriptionList,
                             subscriptionCount,
                             flags,
                             timeoutMs );
}
