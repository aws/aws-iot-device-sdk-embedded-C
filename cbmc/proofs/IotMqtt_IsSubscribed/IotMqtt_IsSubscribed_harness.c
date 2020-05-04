/*
 * IoT MQTT V2.1.0
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file IotMqtt_IsSubscribed_harness.c
 * @brief Implements the proof harness for IotMqtt_IsSubscribed function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

void harness()
{
    IotMqttConnection_t mqttConnection = allocate_IotMqttConnection( NULL );

    __CPROVER_assume( mqttConnection );
    ensure_IotMqttConnection_has_lists( mqttConnection );
    __CPROVER_assume( valid_IotMqttConnection( mqttConnection ) );

    allocate_IotMqttSubscriptionList( &( mqttConnection->subscriptionList ), 1 );
    __CPROVER_assume( valid_IotMqttSubscriptionList( &( mqttConnection->subscriptionList ), 1 ) );

    uint16_t topicFilterLength;
    __CPROVER_assume( topicFilterLength < TOPIC_LENGTH_MAX );

    char * TopicFilter = malloc_can_fail( topicFilterLength );
    __CPROVER_assume( VALID_STRING( TopicFilter, topicFilterLength ) );

    IotMqttSubscription_t result;

    IotMqtt_IsSubscribed( mqttConnection,
                          nondet_bool() ? NULL : TopicFilter,
                          topicFilterLength,
                          nondet_bool() ? NULL : &result );
}
