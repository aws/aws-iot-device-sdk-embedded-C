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
 * @file IotMqtt_PublishSync_harness.c
 * @brief Implements the proof harness for IotMqtt_PublishSync function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"
#include "platform/iot_threads.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

typedef bool ( * MatchFunction_t )( const IotLink_t * const pOperationLink,
                                    void * pCompare );

static unsigned int flagSemaphore;

/**
 * We constrain the return values of these functions because they
 * are checked by assertions in the MQTT code.
 */
IotTaskPoolError_t IotTaskPool_CreateJob( IotTaskPoolRoutine_t userCallback,
                                          void * pUserContext,
                                          IotTaskPoolJobStorage_t * const pJobStorage,
                                          IotTaskPoolJob_t * const pJob )
{
    assert( userCallback != NULL );
    assert( pJobStorage != NULL );
    assert( pJob != NULL );

    /* _IotMqtt_ScheduleOperation asserts this. */
    return IOT_TASKPOOL_SUCCESS;
}

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPool,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs )
{
    IotTaskPoolError_t error;

    /* _IotMqtt_ScheduleOperation asserts this. */
    __CPROVER_assume( error != IOT_TASKPOOL_BAD_PARAMETER &&
                      error != IOT_TASKPOOL_ILLEGAL_OPERATION );
    return error;
}

IotTaskPoolError_t IotTaskPool_TryCancel( IotTaskPool_t taskPool,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus )
{
    if( ( taskPool == NULL ) || ( job == NULL ) )
    {
        return IOT_TASKPOOL_BAD_PARAMETER;
    }

    return IOT_TASKPOOL_SUCCESS;
}

/**
 * _IotMqtt_NextPacketIdentifier calls Atomic_Add_u32, which receives
 * a volatile variable as input. Thus, CBMC will always consider that
 * Atomic_Add_u32 will operate over nondetermistic values and raise
 * a unsigned integer overflow failure. However, developers have reported
 * that the use of this overflow is part of the function implementation.
 * In order to mirror _IotMqtt_NextPacketIdentifier behaviour and avoid
 * spurious alarms, we stub out this function to always
 * return a nondetermistic odd value.
 */
uint16_t _IotMqtt_NextPacketIdentifier( void )
{
    uint16_t id;

    /* Packet identifiers will follow the sequence 1,3,5...65535,1,3,5... */
    __CPROVER_assume( id % 2 == 1 );

    return id;
}

/**
 * We abstract this function for performance reasons. In its original
 * implementation, CBMC ended up creating byte extracts for all possible
 * objects, due to the polymorphic nature of the linked list. We assume
 * that the function is memory safe, and we free and havoc the list to
 * demonstrate that no subsequent code makes use of the values in the list.
 */
void IotListDouble_RemoveAllMatches( const IotListDouble_t * const pList,
                                     MatchFunction_t isMatch,
                                     void * pMatch,
                                     void ( *freeElement )( void * pData ),
                                     size_t linkOffset )
{
    free_IotMqttSubscriptionList( pList );
    allocate_IotMqttSubscriptionList( pList, SUBSCRIPTION_COUNT_MAX - 1 );
}


/**
 * We are abstracting the semaphores because we are doing sequential proof.
 * But the semaphore API assures us that TimedWait called after Post will
 * never fail. Our abstraction of the semaphores models this behavior.
 */
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
    uint32_t timeoutMs;

    /* Initialize semaphore flag. */
    flagSemaphore = 0;

    /* Function under verification. */
    IotMqtt_PublishSync( mqttConnection, /* Always assume a valid connection. */
                         pPublishInfo,
                         flags,
                         timeoutMs );
}
