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
 * @file MQTT_Init_harness.c
 * @brief Implements the proof harness for MQTT_Init function.
 */

#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTContext_t * pContext = NULL;
    MQTTTransportInterface_t * pTransportInterface = NULL;
    MQTTApplicationCallbacks_t * pCallbacks = NULL;
    MQTTFixedBuffer_t * pNetworkBuffer = NULL;

    pContext = mallocCanFail( sizeof( MQTTContext_t ) );
    pTransportInterface = mallocCanFail( sizeof( MQTTContext_t ) );
    pCallbacks = mallocCanFail( sizeof( MQTTApplicationCallbacks_t ) );
    pNetworkBuffer = mallocCanFail( sizeof( MQTTFixedBuffer_t ) );

    MQTT_Init( pContext,
               pTransportInterface,
               pCallbacks,
               pNetworkBuffer );
}
