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
 * @file IotMqtt_Disconnect_harness.c
 * @brief Implements the proof harness for IotMqtt_Disconnect function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

void harness()
{
    IotMqttConnection_t mqttConnection = allocate_IotMqttConnection( NULL );
    uint32_t flags;

    /* Proof assumptions. */
    __CPROVER_assume( mqttConnection != NULL );
    ensure_IotMqttConnection_has_lists( mqttConnection );
    __CPROVER_assume( valid_IotMqttConnection( mqttConnection ) );
    __CPROVER_assume( mqttConnection->references > 0 );
    __CPROVER_assume(
        IMPLIES(
            mqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0,
            mqttConnection->references > 1 ) );
    __CPROVER_assume( mqttConnection->pNetworkInterface != NULL );
    __CPROVER_assume(
        IS_STUBBED_NETWORKIF_SEND( mqttConnection->pNetworkInterface ) );
    __CPROVER_assume(
        IS_STUBBED_NETWORKIF_DESTROY( mqttConnection->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_CLOSE( mqttConnection->pNetworkInterface ) );

    IotMqtt_Disconnect( mqttConnection, flags );
}
