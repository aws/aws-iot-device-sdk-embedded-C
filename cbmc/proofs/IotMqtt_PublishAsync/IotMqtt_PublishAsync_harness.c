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

typedef bool ( * MatchFunction_t )( const IotLink_t * const pOperationLink,
                                    void * pCompare );

typedef void ( * FreeElementFunction_t )( void * pData );

/**
 * We constrain the return values of these functions because
 * they are checked by assertions in the MQTT code.
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

    /* _IotMqtt_ScheduleOperation asserts this */
    __CPROVER_assume( error != IOT_TASKPOOL_BAD_PARAMETER &&
                      error != IOT_TASKPOOL_ILLEGAL_OPERATION );
    return error;
}

/**
 * _IotMqtt_NextPacketIdentifier calls Atomic_Add_u32, which receives
 * a volatile variable as input. Thus, CBMC will always consider that
 * Atomic_Add_u32 will operate over nondetermistic values and raises
 * an unsigned integer overflow failure. However, developers have reported
 * that the use of this overflow is part of the function implementation.
 * In order to mirror _IotMqtt_NextPacketIdentifier behaviour and avoid
 * spurious alarms, we stub out this function to always
 * return a nondetermistic odd value.
 */
uint16_t _IotMqtt_NextPacketIdentifier( void )
{
    uint16_t id;

    /* Packet identifiers will follow the sequence 1,3,5...65535,1,3,5... */
    __CPROVER_assume( id & 0x0001 == 1 );

    return id;
}

/**
 * We assume the list remove functions are memory safe.
 *
 * We abstract the list remove functions for performance reasons.  Our
 * abstraction replaces the original list with an unconstrained list.
 * Our abstraction proves that none of the elements on the original
 * list are accessed after the remove: We free all elements on the
 * original list, so that any later access will be caught as a
 * use-after-free error.
 */
void IotListDouble_RemoveAllMatches( const IotListDouble_t * const pList,
                                     MatchFunction_t isMatch,
                                     void * pMatch,
                                     FreeElementFunction_t freeElement,
                                     size_t linkOffset )
{
    free_IotMqttSubscriptionList( pList );
    allocate_IotMqttSubscriptionList( pList, SUBSCRIPTION_COUNT_MAX - 1 );
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
