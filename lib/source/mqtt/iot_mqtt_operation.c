/*
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
 * @file iot_mqtt_operation.c
 * @brief Implements functions that process MQTT operations.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <string.h>

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/*-----------------------------------------------------------*/

/**
 * @brief First parameter to #_mqttOperation_match.
 */
typedef struct _operationMatchParam
{
    IotMqttOperationType_t operation;   /**< @brief The operation to look for. */
    const uint16_t * pPacketIdentifier; /**< @brief The packet identifier associated with the operation.
                                         * Set to `NULL` to ignore packet identifier. */
} _operationMatchParam_t;

/*-----------------------------------------------------------*/

/**
 * @brief Match an MQTT operation by type and packet identifier.
 *
 * @param[in] pOperationLink Pointer to the link member of an #_mqttOperation_t.
 * @param[in] pMatch Pointer to an #_operationMatchParam_t.
 *
 * @return `true` if the operation matches the parameters in `pArgument`; `false`
 * otherwise.
 */
static bool _mqttOperation_match( const IotLink_t * pOperationLink,
                                  void * pMatch );

/*-----------------------------------------------------------*/

/**
 * @brief The task pool that processes MQTT operations.
 */
IotTaskPool_t _IotMqttTaskPool = { 0 };

/*-----------------------------------------------------------*/

static bool _mqttOperation_match( const IotLink_t * pOperationLink,
                                  void * pMatch )
{
    bool match = false;
    _mqttOperation_t * pOperation = IotLink_Container( _mqttOperation_t,
                                                       pOperationLink,
                                                       link );
    _operationMatchParam_t * pParam = ( _operationMatchParam_t * ) pMatch;

    /* Check for matching operations. */
    if( pParam->operation == pOperation->operation )
    {
        /* Check for matching packet identifiers. */
        if( pParam->pPacketIdentifier == NULL )
        {
            match = true;
        }
        else
        {
            match = ( *( pParam->pPacketIdentifier ) == pOperation->packetIdentifier );
        }
    }

    return match;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_CreateOperation( _mqttOperation_t ** const pNewOperation,
                                         uint32_t flags,
                                         const IotMqttCallbackInfo_t * const pCallbackInfo )
{
    _mqttOperation_t * pOperation = NULL;

    IotLogDebug( "Creating new MQTT operation record." );

    /* If the waitable flag is set, make sure that there's no callback. */
    if( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
    {
        if( pCallbackInfo != NULL )
        {
            IotLogError( "Callback should not be set for a waitable operation." );

            return IOT_MQTT_BAD_PARAMETER;
        }
    }

    /* Allocate memory for a new operation. */
    pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

    if( pOperation == NULL )
    {
        IotLogError( "Failed to allocate memory for new MQTT operation." );

        return IOT_MQTT_NO_MEMORY;
    }

    /* Clear the operation data. */
    ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );

    /* Check if the waitable flag is set. If it is, create a semaphore to
     * wait on. */
    if( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
    {
        /* The wait semaphore counts up to 2: once for when the send thread completes,
         * and once for when the entire operation completes. */
        if( IotSemaphore_Create( &( pOperation->notify.waitSemaphore ), 0, 2 ) == false )
        {
            IotLogError( "Failed to create semaphore for waitable MQTT operation." );

            IotMqtt_FreeOperation( pOperation );

            return IOT_MQTT_NO_MEMORY;
        }
    }
    else
    {
        /* If the waitable flag isn't set but a callback is, copy the callback
         * information. */
        if( pCallbackInfo != NULL )
        {
            pOperation->notify.callback = *pCallbackInfo;
        }
    }

    /* Initialize the flags and status members of the new operation. */
    pOperation->flags = flags;
    pOperation->status = IOT_MQTT_STATUS_PENDING;

    /* Set the output parameter. */
    *pNewOperation = pOperation;

    return IOT_MQTT_SUCCESS;
}

/*-----------------------------------------------------------*/

void _IotMqtt_DestroyOperation( void * pData )
{
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) pData;

    IotLogDebug( "Destroying operation %s.",
                 IotMqtt_OperationType( pOperation->operation ) );

    /* If the MQTT packet is still allocated, free it. */
    if( pOperation->pMqttPacket != NULL )
    {
        /* Choose a free packet function. */
        void ( * freePacket )( uint8_t * ) = _IotMqtt_FreePacket;

        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pOperation->pMqttConnection->network.freePacket != NULL )
            {
                freePacket = pOperation->pMqttConnection->network.freePacket;
            }
        #endif

        freePacket( pOperation->pMqttPacket );
    }

    /* Check if a wait semaphore was created for this operation. */
    if( ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
    {
        IotSemaphore_Destroy( &( pOperation->notify.waitSemaphore ) );
    }

    /* Free the memory used to hold operation data. */
    IotMqtt_FreeOperation( pOperation );
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessKeepAlive( IotTaskPool_t * pTaskPool,
                                IotTaskPoolJob_t * pKeepAliveJob,
                                void * pContext )
{
    bool status = true;

    /* Retrieve the MQTT connection from the context. */
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t* ) pContext;

    /* Check parameters. The task pool and job parameter is not used when asserts
     * are disabled. */
    ( void ) pTaskPool;
    ( void ) pKeepAliveJob;
    IotMqtt_Assert( pTaskPool == &( _IotMqttTaskPool ) );
    IotMqtt_Assert( pKeepAliveJob == &( pMqttConnection->keepAliveJob ) );

    /* Check that keep-alive interval is valid. The MQTT spec states its maximum
     * value is 65,535 seconds. */
    IotMqtt_Assert( pMqttConnection->keepAliveMs <= 65535000 );

    IotLogDebug( "Keep-alive job started." );

    /* Read the current keep-alive status. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    status = ( pMqttConnection->keepAliveFailure == false );

    if( status == true )
    {
        IotLogDebug( "Sending PINGREQ." );

        /* Because PINGREQ may be used to keep the MQTT connection alive, it is
         * more important than other operations. Bypass the queue of jobs for
         * operations by directly sending the PINGREQ in this job. */
        if( pMqttConnection->network.send( pMqttConnection->network.pSendContext,
                                           pMqttConnection->pPingreqPacket,
                                           pMqttConnection->pingreqPacketSize ) != pMqttConnection->pingreqPacketSize )
        {
            IotLogError( "Failed to send PINGREQ." );
            status = false;
        }
        else
        {
            /* Assume the keep-alive will fail. The network receive callback will
             * clear the failure flag upon receiving a PINGRESP. */
            pMqttConnection->keepAliveFailure = true;
        }
    }
    else
    {
        IotLogError( "Failed to receive PINGRESP within %d ms.", IOT_MQTT_RESPONSE_WAIT_MS );

        /* Mark the connection as disconnected because of PINGREQ failure. */
        pMqttConnection->disconnected = true;

        /* Clean up PINGREQ packet and job. */
        _IotMqtt_FreePacket( pMqttConnection->pPingreqPacket );
        IotTaskPool_DestroyJob( &( _IotMqttTaskPool ),
                                &( pMqttConnection->keepAliveJob ) );

        /* Clear data about the keep-alive. */
        pMqttConnection->keepAliveMs = 0;
        pMqttConnection->pPingreqPacket = NULL;
        pMqttConnection->pingreqPacketSize = 0;
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* When a PINGREQ is successfully sent, reschedule this job to check for a
     * response shortly. Otherwise, decrement the reference count for the MQTT
     * connection since the PINGREQ has failed and will no longer use the connection. */
    if( status == true )
    {
        IotLogDebug( "Rescheduling keep-alive job to check for PINGRESP in %d ms.",
                     IOT_MQTT_RESPONSE_WAIT_MS );

        IotTaskPool_ScheduleDeferred( &( _IotMqttTaskPool ),
                                      &( pMqttConnection->keepAliveJob ),
                                      IOT_MQTT_RESPONSE_WAIT_MS );
    }
    else
    {
        _IotMqtt_DecrementConnectionReferences( pMqttConnection );

        IotLogDebug( "Failed keep-alive job has been cleaned up." );
    }
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessIncomingPublish( IotTaskPool_t * pTaskPool,
                                      IotTaskPoolJob_t * pPublishJob,
                                      void * pContext )
{
    _mqttOperation_t * pCurrent = NULL, * pNext = pContext;
    IotMqttCallbackParam_t callbackParam = { .message = { 0 } };

    /* Check parameters. The task pool and job parameter is not used when asserts
     * are disabled. */
    ( void ) pTaskPool;
    ( void ) pPublishJob;
    IotMqtt_Assert( pTaskPool == &( _IotMqttTaskPool ) );
    IotMqtt_Assert( pNext->incomingPublish == true );
    IotMqtt_Assert( pPublishJob == &( pNext->job ) );

    /* Process each linked incoming PUBLISH. */
    while( pNext != NULL )
    {
        /* Save a pointer to the current PUBLISH and move the iterating
         * pointer. */
        pCurrent = pNext;
        pNext = pNext->pNextPublish;

        /* Process the current PUBLISH. */
        if( ( pCurrent->publishInfo.pPayload != NULL ) &&
            ( pCurrent->publishInfo.pTopicName != NULL ) )
        {
            callbackParam.message.info = pCurrent->publishInfo;

            _IotMqtt_InvokeSubscriptionCallback( pCurrent->pMqttConnection,
                                                 &callbackParam );
        }

        /* Free any buffers associated with the current PUBLISH message. */
        if( pCurrent->freeReceivedData != NULL )
        {
            IotMqtt_Assert( pCurrent->pReceivedData != NULL );
            pCurrent->freeReceivedData( ( void * ) pCurrent->pReceivedData );
        }

        /* Free the current PUBLISH. */
        IotMqtt_FreeOperation( pCurrent );
    }
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessSend( IotTaskPool_t * pTaskPool,
                           IotTaskPoolJob_t * pSendJob,
                           void * pContext )
{
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessCompletedOperation( IotTaskPool_t * pTaskPool,
                                         IotTaskPoolJob_t * pOperationJob,
                                         void * pContext )
{
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_ScheduleOperation( _mqttOperation_t * const pOperation,
                                           IotTaskPoolRoutine_t jobRoutine )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;

    /* Check that job routine is valid. */
    IotMqtt_Assert( ( jobRoutine == _IotMqtt_ProcessSend ) ||
                    ( jobRoutine == _IotMqtt_ProcessCompletedOperation ) ||
                    ( jobRoutine == _IotMqtt_ProcessIncomingPublish ) );

    /* Creating a new job should never fail when parameters are valid. */
    taskPoolStatus = IotTaskPool_CreateJob( jobRoutine,
                                            pOperation,
                                            &( pOperation->job ) );
    IotMqtt_Assert( taskPoolStatus == IOT_TASKPOOL_SUCCESS );

    /* Schedule the new job. */
    taskPoolStatus = IotTaskPool_Schedule( &( _IotMqttTaskPool ), &( pOperation->job ) );

    if( taskPoolStatus != IOT_TASKPOOL_SUCCESS )
    {
        /* Scheduling a newly-created job should never be invalid or illegal. */
        IotMqtt_Assert( taskPoolStatus != IOT_TASKPOOL_BAD_PARAMETER );
        IotMqtt_Assert( taskPoolStatus != IOT_TASKPOOL_ILLEGAL_OPERATION );

        IotLogWarn( "Failed to schedule MQTT operation, status %d.",
                    taskPoolStatus );

        status = IOT_MQTT_SCHEDULING_ERROR;
    }

    return status;
}

/*-----------------------------------------------------------*/

_mqttOperation_t * _IotMqtt_FindOperation( _mqttConnection_t * const pMqttConnection,
                                           IotMqttOperationType_t operation,
                                           const uint16_t * const pPacketIdentifier )
{
    _mqttOperation_t * pResult = NULL;
    _operationMatchParam_t param = { 0 };

    IotLogDebug( "Searching for in-progress operation %s in MQTT operations pending response.",
                 IotMqtt_OperationType( operation ) );

    if( pPacketIdentifier != NULL )
    {
        IotLogDebug( "Searching for packet identifier %hu.", *pPacketIdentifier );
    }

    /* Set the search parameters. */
    param.operation = operation;
    param.pPacketIdentifier = pPacketIdentifier;

    /* Find the first matching element in the list. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    pResult = IotLink_Container( _mqttOperation_t,
                                 IotListDouble_RemoveFirstMatch( &( pMqttConnection->pendingResponse ),
                                                                 NULL,
                                                                 _mqttOperation_match,
                                                                 &param ),
                                 link );
    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* The result will be NULL if no corresponding operation was found in the
     * list. */
    if( pResult == NULL )
    {
        IotLogDebug( "In-progress operation %s not found.",
                     IotMqtt_OperationType( operation ) );
    }
    else
    {
        IotLogDebug( "Found in-progress operation %s.",
                     IotMqtt_OperationType( operation ) );
    }

    return pResult;
}

/*-----------------------------------------------------------*/

void _IotMqtt_Notify( _mqttOperation_t * const pOperation )
{
    /* Remove any lingering subscriptions if a SUBSCRIBE failed. Rejected
     * subscriptions are removed by the deserializer, so not removed here. */
    if( ( pOperation->operation == IOT_MQTT_SUBSCRIBE ) &&
        ( pOperation->status != IOT_MQTT_SUCCESS ) &&
        ( pOperation->status != IOT_MQTT_SERVER_REFUSED ) )
    {
        _IotMqtt_RemoveSubscriptionByPacket( pOperation->pMqttConnection,
                                             pOperation->packetIdentifier,
                                             -1 );
    }

    /* If the operation is waitable, post to its wait semaphore and return.
     * Otherwise, enqueue it for callback. */
    if( ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
    {
        IotSemaphore_Post( &( pOperation->notify.waitSemaphore ) );
    }
    else
    {
        if( pOperation->notify.callback.function != NULL )
        {
            if( _IotMqtt_ScheduleOperation( pOperation,
                                            _IotMqtt_ProcessCompletedOperation ) != IOT_MQTT_SUCCESS )
            {
                IotLogWarn( "Failed to create new callback thread." );
            }
        }
        else
        {
            /* Destroy the operation if no callback was set. */
            _IotMqtt_DestroyOperation( pOperation );
        }
    }
}

/*-----------------------------------------------------------*/
