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
 * @file MQTT_ProcessLoop_harness.c
 * @brief Implements the proof harness for MQTT_ProcessLoop function.
 */
#include "mqtt.h"
#include "mqtt_cbmc_state.h"
#include "network_interface_stubs.h"
#include "get_time_stub.h"
#include "event_callback_stub.h"

void harness()
{
    MQTTContext_t * pContext;
    uint32_t timeout;

    /* TODO: This should all go into allocating the MQTTContext_t. */
    TransportInterface_t * pTransportInterface;
    MQTTApplicationCallbacks_t * pCallbacks;
    MQTTFixedBuffer_t * pNetworkBuffer;
    MQTTStatus_t status = MQTTSuccess;

    pContext = allocateMqttContext( NULL );
    __CPROVER_assume( isValidMqttContext( pContext ) );

    pTransportInterface = mallocCanFail( sizeof( TransportInterface_t ) );

    if( pTransportInterface != NULL )
    {
        pTransportInterface->recv = NetworkInterfaceReceiveStub;
        pTransportInterface->send = NetworkInterfaceSendStub;
    }

    pCallbacks = mallocCanFail( sizeof( MQTTApplicationCallbacks_t ) );

    if( pCallbacks )
    {
        pCallbacks->getTime = GetCurrentTimeStub;
        pCallbacks->appCallback = EventCallbackStub;
    }

    pNetworkBuffer = allocateMqttFixedBuffer( NULL );
    __CROVER_assume( isValidMqttFixedBuffer( pNetworkBuffer ) );

    /* It is part of the API contract to call MQTT_Init() before any other
     * function in mqtt.h. */
    if( pContext != NULL )
    {
        status = MQTT_Init( pContext, pTransportInterface, pCallbacks, pNetworkBuffer );
    }

    if( status == MQTTSuccess )
    {
        /* For coverage, it is expected that a NULL pContext will reach this
         * function. */
        MQTT_ProcessLoop( pContext, MQTT_PROCESS_LOOP_TIMEOUT );
    }
}
