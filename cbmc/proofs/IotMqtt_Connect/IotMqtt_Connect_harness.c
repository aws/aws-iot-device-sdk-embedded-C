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

typedef bool ( * MatchFunction_t )( const IotLink_t * const pOperationLink,
                                    void * pCompare );

typedef void ( * FreeElementFunction_t )( void * pData );

/**
 * We constrain the return values of this function because it
 * is checked by assertions in the MQTT code.
 */
IotTaskPoolError_t IotTaskPool_TryCancel( IotTaskPool_t taskPool,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus )
{
    assert( ( taskPool == NULL ) || ( job == NULL ) );
    return IOT_TASKPOOL_BAD_PARAMETER;
}

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

void _IotMqtt_RemoveSubscriptionByTopicFilter( _mqttConnection_t * pMqttConnection,
                                               const IotMqttSubscription_t * pSubscriptionList,
                                               size_t subscriptionCount )
{
    free_IotMqttSubscriptionList( &( pMqttConnection->subscriptionList ) );
    allocate_IotMqttSubscriptionList( &( pMqttConnection->subscriptionList ), subscriptionCount );
}

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
