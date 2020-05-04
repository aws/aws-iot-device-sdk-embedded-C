/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file IotMqtt_PublishAsync_harness.c
 * @brief Implements the proof harness for IotMqtt_PublishAsync function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

void harness()
{
    /* Assume a valid MQTT connection. */
    IotMqttConnection_t mqttConnection = allocate_IotMqttConnection( NULL );

    __CPROVER_assume( mqttConnection != NULL );
    __CPROVER_assume( mqttConnection->pNetworkInterface != NULL );
    __CPROVER_assume( IS_STUBBED_NETWORKIF_SEND( mqttConnection->pNetworkInterface ) );
    __CPROVER_assume( IS_STUBBED_NETWORKIF_DESTROY( mqttConnection->pNetworkInterface ) );
    ensure_IotMqttConnection_has_lists( mqttConnection );
    __CPROVER_assume( valid_IotMqttConnection( mqttConnection ) );


    /* Assume a valid publish info. */
    IotMqttPublishInfo_t * pPublishInfo = allocate_IotMqttPublishInfo( NULL );
    __CPROVER_assume( IMPLIES( pPublishInfo != NULL, valid_IotMqttPublishInfo( pPublishInfo ) ) );

    /* Assume unconstrained inputs. */
    uint32_t flags;
    IotMqttCallbackInfo_t * callbackInfo = malloc_can_fail( sizeof( *callbackInfo ) );

    /* Output. */
    IotMqttOperation_t * publishOperation = malloc_can_fail( sizeof( *publishOperation ) );


    /* Function under verification. */
    IotMqttError_t status = IotMqtt_PublishAsync( mqttConnection,
                                                  pPublishInfo,
                                                  flags,
                                                  callbackInfo,
                                                  publishOperation );
    /* Post-conditions. */
    assert( IMPLIES( status == IOT_MQTT_STATUS_PENDING,
                     pPublishInfo->qos == IOT_MQTT_QOS_1 ) );
    assert( IMPLIES( status == IOT_MQTT_SUCCESS,
                     pPublishInfo->qos == IOT_MQTT_QOS_0 ||
                     pPublishInfo->qos == IOT_MQTT_QOS_1 ) );
}
