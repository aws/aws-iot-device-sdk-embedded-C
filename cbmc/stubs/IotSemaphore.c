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
 * @file IotSemaphore.c
 * @brief Implements stubs for IotSemaphore_* functions.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include "mqtt_state.h"

/*
 * We assume the IoT Semaphore operations are memory safe.
 *
 * We abstract the semaphores because we are doing sequential proof.
 * But the semaphore API assures us that TimedWait called after Post will
 * never fail. Our abstraction of the semaphores models this behavior.
 *
 * Our abstraction is safe because the Disconnect method invokes the
 * semaphore methods on the semaphore associated with the Disconnect
 * packet.  The Disconnect method is the only code that accesses this
 * semaphore.  This justifies this simple semaphore model of checking
 * for Post before TimedWait.
 */

static unsigned int flagSemaphore;

bool IotSemaphore_Create( IotSemaphore_t * pNewSemaphore,
                          uint32_t initialValue,
                          uint32_t maxValue )
{
    if( nondet_bool() )
    {
        __CPROVER_assume( flagSemaphore == 0 );
        return true;
    }

    return false;
}

void IotSemaphore_Post( IotSemaphore_t * pSemaphore )
{
    assert( pSemaphore != NULL );
    flagSemaphore++;
}

bool IotSemaphore_TimedWait( IotSemaphore_t * pSemaphore,
                             uint32_t timeoutMs )
{
    assert( pSemaphore != NULL );

    if( flagSemaphore > 0 )
    {
        flagSemaphore--;
        return true;
    }

    return false;
}
