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
 * @file IotMqtt_Connect_harness.c
 * @brief Implements the proof harness for IotMqtt_Connect function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"
#include "iot_mqtt_protocol.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

void harness()
{
    /* Assume a valid NetworkInfo_t. */
    IotMqttNetworkInfo_t * pNetworkInfo = allocate_IotMqttNetworkInfo( NULL );

    __CPROVER_assume( IMPLIES( pNetworkInfo != NULL,
                               pNetworkInfo->pNetworkInterface != NULL &&
                               IS_STUBBED_NETWORKIF_CREATE( pNetworkInfo->pNetworkInterface ) &&
                               IS_STUBBED_NETWORKIF_SEND( pNetworkInfo->pNetworkInterface ) &&
                               IS_STUBBED_NETWORKIF_CLOSE( pNetworkInfo->pNetworkInterface ) &&
                               IS_STUBBED_NETWORKIF_DESTROY( pNetworkInfo->pNetworkInterface ) &&
                               IS_STUBBED_NETWORKIF_SETRECEIVECALLBACK( pNetworkInfo->pNetworkInterface ) &&
                               valid_IotMqttNetworkInfo( pNetworkInfo ) ) );

    /* Assume a valid ConnectInfo_t. */
    IotMqttConnectInfo_t * pConnectInfo = allocate_IotMqttConnectInfo( NULL );
    __CPROVER_assume( IMPLIES( pConnectInfo != NULL,
                               valid_IotMqttConnectInfo( pConnectInfo ) ) );

    /* Assume a unconstrained timeout. */
    uint32_t timeoutMs;

    /* Assume a valid MQTT connection. */
    IotMqttConnection_t pMqttConnection = allocate_IotMqttConnection( NULL );

    /* Operation under verification. */
    IotMqttError_t status = IotMqtt_Connect( pNetworkInfo, pConnectInfo, timeoutMs, pMqttConnection );
}
