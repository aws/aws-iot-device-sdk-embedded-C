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
 * @file IotMqtt_Notify_harness.c
 * @brief Implements the proof harness for _IotMqtt_Notify function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"
#include "platform/iot_threads.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

void harness()
{
    /* Assume a valid MQTT connection. */
    IotMqttConnection_t pMqttConnection = allocate_IotMqttConnection( NULL );

    __CPROVER_assume( pMqttConnection != NULL );
    __CPROVER_assume( pMqttConnection->pNetworkInterface != NULL );
    __CPROVER_assume( IS_STUBBED_NETWORKIF_SEND( pMqttConnection->pNetworkInterface ) );
    __CPROVER_assume( IS_STUBBED_NETWORKIF_DESTROY( pMqttConnection->pNetworkInterface ) );
    ensure_IotMqttConnection_has_lists( pMqttConnection );
    __CPROVER_assume( valid_IotMqttConnection( pMqttConnection ) );

    /* If there are no operations waiting on this connection, then there is nothing
     * to notify, so assume references is positive. */
    __CPROVER_assume( pMqttConnection->references > 0 );

    /* Assume unconstrained operation. */
    IotMqttOperation_t pOperation = allocate_IotMqttOperation( NULL, pMqttConnection );
    __CPROVER_assume( valid_IotMqttOperation( pOperation ) );

    /* Inbound packets are either an inbound publish or an inbound response
     * (a ping response or an acknowledgement). The purpose of _IotMqtt_Notify
     * is to alert any task waiting on an inbound response. _IotMqtt_Notify is
     * never invoked on an inbound publish, so assume incomingPublish is false. */
    __CPROVER_assume( pOperation->incomingPublish == false );
    IotListDouble_Create( &( pOperation->link ) );

    if( nondet_bool() )
    {
        IotListDouble_InsertHead( &( pMqttConnection->pendingProcessing ), &( pOperation->link ) );
    }

    /* Function under verification. */
    _IotMqtt_Notify( pOperation );
}
