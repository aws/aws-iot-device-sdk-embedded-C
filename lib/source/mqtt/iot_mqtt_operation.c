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

/**
 * @brief Schedule the next send of an operation with retry.
 *
 * @param[in] pOperation The operation to retry.
 */
static IotMqttError_t _scheduleNextRetry( _mqttOperation_t * pOperation );

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

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    IotMqtt_Assert( pOperationLink != NULL );

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

static IotMqttError_t _scheduleNextRetry( _mqttOperation_t * pOperation )
{
    return IOT_MQTT_SCHEDULING_ERROR;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_CreateOperation( _mqttConnection_t * const pMqttConnection,
                                         uint32_t flags,
                                         const IotMqttCallbackInfo_t * const pCallbackInfo,
                                         _mqttOperation_t ** const pNewOperation )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttOperation_t * pOperation = NULL;
    bool waitable = ( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE );

    /* If the waitable flag is set, make sure that there's no callback. */
    if( waitable == true )
    {
        _validateParameter( ( pCallbackInfo == NULL ),
                            "Callback should not be set for a waitable operation." );
    }

    IotLogDebug( "Creating new MQTT operation record." );

    /* Increment the reference count for the MQTT connection when creating a new
     * operation. */
    if( _IotMqtt_IncrementConnectionReferences( pMqttConnection ) == false )
    {
        IotLogError( "New MQTT operation record cannot be created for a closed connection" );
        status = IOT_MQTT_NETWORK_ERROR;

        goto errorIncrementReferences;
    }

    /* Allocate memory for a new operation. */
    pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

    if( pOperation == NULL )
    {
        IotLogError( "Failed to allocate memory for new MQTT operation." );
        status = IOT_MQTT_NO_MEMORY;

        goto errorMallocOperation;
    }

    /* Clear the operation data. */
    ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );

    /* Initialize the some members of the new operation. */
    pOperation->pMqttConnection = pMqttConnection;
    pOperation->jobReference = 1;
    pOperation->flags = flags;
    pOperation->status = IOT_MQTT_STATUS_PENDING;

    /* Check if the waitable flag is set. If it is, create a semaphore to
     * wait on. */
    if( waitable == true )
    {
        /* Create a semaphore to wait on for a waitable operation. */
        if( IotSemaphore_Create( &( pOperation->notify.waitSemaphore ), 0, 1 ) == false )
        {
            IotLogError( "Failed to create semaphore for waitable MQTT operation." );
            status = IOT_MQTT_NO_MEMORY;

            goto errorCreateSemaphore;
        }

        /* A waitable operation is created with an additional reference for the
         * Wait function. */
        ( pOperation->jobReference )++;
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

    /* Add this operation to the MQTT connection's operation list. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    IotListDouble_InsertHead( &( pMqttConnection->pendingProcessing ),
                              &( pOperation->link ) );
    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Set the output parameter. */
    *pNewOperation = pOperation;

    /* This is the successful return path. */
    IotMqtt_Assert( status == IOT_MQTT_SUCCESS );

    return status;

errorCreateSemaphore: IotMqtt_FreeOperation( pOperation );
errorMallocOperation: _IotMqtt_DecrementConnectionReferences( pMqttConnection );
errorIncrementReferences: return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_DecrementOperationReferences( _mqttOperation_t * pOperation,
                                            bool cancelJob )
{
    bool destroyOperation = false;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* Attempt to cancel the operation's job. */
    if( cancelJob == true )
    {
        taskPoolStatus = IotTaskPool_TryCancel( &( _IotMqttTaskPool ),
                                                &( pOperation->job ),
                                                NULL );

        /* If the operation's job was not canceled, it must be already executing.
         * Any other return value is invalid. */
        IotMqtt_Assert( ( taskPoolStatus == IOT_TASKPOOL_SUCCESS ) ||
                        ( taskPoolStatus == IOT_TASKPOOL_CANCEL_FAILED ) );
    }

    /* Decrement job reference count. */
    if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
    {
        IotLogDebug( "Job of %s operation %p (MQTT connection %p) canceled.",
                     IotMqtt_OperationType( pOperation->operation ),
                     pOperation,
                     pMqttConnection );

        IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
        pOperation->jobReference--;

        /* The job reference count must be 0 or 1 after the decrement. */
        IotMqtt_Assert( ( pOperation->jobReference == 0 ) ||
                        ( pOperation->jobReference == 1 ) );

        /* This operation may be destroyed if its reference count is 0. */
        if( pOperation->jobReference == 0 )
        {
            destroyOperation = true;
        }

        IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
    }

    return destroyOperation;
}

/*-----------------------------------------------------------*/

void _IotMqtt_DestroyOperation( _mqttOperation_t * pOperation )
{
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* Default free packet function. */
    void ( * freePacket )( uint8_t * ) = _IotMqtt_FreePacket;

    IotLogDebug( "Destroying %s operation %p (MQTT connection %p).",
                 IotMqtt_OperationType( pOperation->operation ),
                 pOperation,
                 pMqttConnection );

    /* The job reference count must be between 0 and 2. */
    IotMqtt_Assert( ( pOperation->jobReference >= 0 ) &&
                    ( pOperation->jobReference <= 2 ) );

    /* Jobs to be destroyed should be removed from the MQTT connection's
     * lists. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    if( IotLink_IsLinked( &( pOperation->link ) ) == true )
    {
        IotLogDebug( "Removed %s operation %p from lists of MQTT connection %p.",
                     IotMqtt_OperationType( pOperation->operation ),
                     pOperation,
                     pMqttConnection );

        IotListDouble_Remove( &( pOperation->link ) );
    }
    else
    {
        IotLogDebug( "%s operation %p was not present in lists of MQTT connection %p.",
                     IotMqtt_OperationType( pOperation->operation ),
                     pOperation,
                     pMqttConnection );
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Free any allocated MQTT packet. */
    if( pOperation->pMqttPacket != NULL )
    {
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pMqttConnection->network.freePacket != NULL )
            {
                freePacket = pMqttConnection->network.freePacket;
            }
        #endif

        freePacket( pOperation->pMqttPacket );

        IotLogDebug( "MQTT packet of %s operation %p (MQTT connection %p) freed.",
                     IotMqtt_OperationType( pOperation->operation ),
                     pOperation,
                     pMqttConnection );
    }
    else
    {
        IotLogDebug( "%s operation %p (MQTT connection %p) has no allocated MQTT packet.",
                     IotMqtt_OperationType( pOperation->operation ),
                     pOperation,
                     pMqttConnection );
    }

    /* Check if a wait semaphore was created for this operation. */
    if( ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
    {
        IotSemaphore_Destroy( &( pOperation->notify.waitSemaphore ) );

        IotLogDebug( "Wait semaphore of %s operation %p (MQTT connection %p) destroyed.",
                     IotMqtt_OperationType( pOperation->operation ),
                     pOperation,
                     pMqttConnection );
    }

    IotLogDebug( "%s operation %p (MQTT connection %p) destroyed.",
                 IotMqtt_OperationType( pOperation->operation ),
                 pOperation,
                 pMqttConnection );

    /* Free the memory used to hold operation data. */
    IotMqtt_FreeOperation( pOperation );

    /* Decrement the MQTT connection's reference count after destroying an
     * operation. */
    _IotMqtt_DecrementConnectionReferences( pMqttConnection );
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessKeepAlive( IotTaskPool_t * pTaskPool,
                                IotTaskPoolJob_t * pKeepAliveJob,
                                void * pContext )
{
    bool status = true;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;

    /* Retrieve the MQTT connection from the context. */
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) pContext;

    /* Check parameters. */
    IotMqtt_Assert( pTaskPool == &( _IotMqttTaskPool ) );
    IotMqtt_Assert( pKeepAliveJob == &( pMqttConnection->keepAliveJob ) );

    /* Check that keep-alive interval is valid. The MQTT spec states its maximum
     * value is 65,535 seconds. */
    IotMqtt_Assert( pMqttConnection->keepAliveMs <= 65535000 );

    /* Only two values are valid for the next keep alive job delay. */
    IotMqtt_Assert( ( pMqttConnection->nextKeepAliveMs == pMqttConnection->keepAliveMs ) ||
                    ( pMqttConnection->nextKeepAliveMs == IOT_MQTT_RESPONSE_WAIT_MS ) );

    IotLogDebug( "Keep-alive job started for MQTT connection %p.", pMqttConnection );

    /* Re-create the keep-alive job for rescheduling. This should never fail. */
    taskPoolStatus = IotTaskPool_CreateJob( _IotMqtt_ProcessKeepAlive,
                                            pContext,
                                            pKeepAliveJob );
    IotMqtt_Assert( taskPoolStatus == IOT_TASKPOOL_SUCCESS );

    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    /* Determine whether to send a PINGREQ or check for PINGRESP. */
    if( pMqttConnection->nextKeepAliveMs == pMqttConnection->keepAliveMs )
    {
        IotLogDebug( "Sending PINGREQ for MQTT connection %p.", pMqttConnection );

        /* Because PINGREQ may be used to keep the MQTT connection alive, it is
         * more important than other operations. Bypass the queue of jobs for
         * operations by directly sending the PINGREQ in this job. */
        if( pMqttConnection->network.send( pMqttConnection->network.pSendContext,
                                           pMqttConnection->pPingreqPacket,
                                           pMqttConnection->pingreqPacketSize ) != pMqttConnection->pingreqPacketSize )
        {
            IotLogError( "Failed to send PINGREQ for MQTT connection %p.", pMqttConnection );
            status = false;
        }
        else
        {
            /* Assume the keep-alive will fail. The network receive callback will
             * clear the failure flag upon receiving a PINGRESP. */
            pMqttConnection->keepAliveFailure = true;

            /* Schedule a check for PINGRESP. */
            pMqttConnection->nextKeepAliveMs = IOT_MQTT_RESPONSE_WAIT_MS;

            IotLogDebug( "PINGREQ sent for MQTT connection %p. Scheduling check "
                         "for PINGRESP in %d ms.",
                         pMqttConnection,
                         IOT_MQTT_RESPONSE_WAIT_MS );
        }
    }
    else
    {
        IotLogDebug( "Checking for PINGRESP for MQTT connection %p.", pMqttConnection );

        if( pMqttConnection->keepAliveFailure == false )
        {
            IotLogDebug( "PINGRESP was received for MQTT connection %p.", pMqttConnection );

            /* PINGRESP was received. Schedule the next PINGREQ transmission. */
            pMqttConnection->nextKeepAliveMs = pMqttConnection->keepAliveMs;
        }
        else
        {
            IotLogError( "Failed to receive PINGRESP within %d ms for MQTT "
                         "connection %p.",
                         pMqttConnection,
                         IOT_MQTT_RESPONSE_WAIT_MS );

            /* The network receive callback did not clear the failure flag. */
            status = false;
        }
    }

    /* When a PINGREQ is successfully sent, reschedule this job to check for a
     * response shortly. */
    if( status == true )
    {
        taskPoolStatus = IotTaskPool_ScheduleDeferred( pTaskPool,
                                                       pKeepAliveJob,
                                                       pMqttConnection->nextKeepAliveMs );

        if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
        {
            IotLogDebug( "Rescheduled keep-alive job for MQTT connection %p to "
                         "check for PINGRESP in %d ms.",
                         pMqttConnection,
                         IOT_MQTT_RESPONSE_WAIT_MS );
        }
        else
        {
            IotLogError( "Failed to reschedule keep-alive job for PINGRESP check "
                         "for MQTT connection %p.",
                         pMqttConnection );

            status = false;
        }
    }

    /* Close the connection on failures. */
    if( status == false )
    {
        _IotMqtt_CloseNetworkConnection( pMqttConnection );
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
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
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) pContext;
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    IotLogDebug( "Send job started for %s operation %p.",
                 IotMqtt_OperationType( pOperation->operation ),
                 pOperation );

    /* The given operation must have an allocated packet and be waiting for a status. */
    IotMqtt_Assert( pOperation->pMqttPacket != NULL );
    IotMqtt_Assert( pOperation->packetSize != 0 );
    IotMqtt_Assert( pOperation->jobReference >= 1 );
    IotMqtt_Assert( pOperation->status == IOT_MQTT_STATUS_PENDING );

    /* Check if operation with retry has reached its limit. */
    if( pOperation->retry.limit > 0 )
    {
        /* Only PUBLISH may be retried. */
        IotMqtt_Assert( pOperation->operation == IOT_MQTT_PUBLISH_TO_SERVER );

        if( pOperation->retry.count == pOperation->retry.limit )
        {
            pOperation->status = IOT_MQTT_RETRY_NO_RESPONSE;
        }
    }
    else
    {
        /* Transmit the MQTT packet from the operation over the network. */
        if( pMqttConnection->network.send( pMqttConnection->network.pSendContext,
                                           pOperation->pMqttPacket,
                                           pOperation->packetSize ) != pOperation->packetSize )
        {
            IotLogError( "Failed to send MQTT packet for %s operation %p.",
                         IotMqttOperationType( pOperation->operation ),
                         pOperation );

            pOperation->status = IOT_MQTT_NETWORK_ERROR;
        }
        else
        {
            /* DISCONNECT operations are considered successful upon successful
             * transmission. */
            if( pOperation->operation == IOT_MQTT_DISCONNECT )
            {
                pOperation->status = IOT_MQTT_SUCCESS;
            }
            /* Move other operations from pending processing to pending response. */
            else
            {
                if( pOperation->retry.limit > 0 )
                {
                    pOperation->status = _scheduleNextRetry( pOperation );
                }
                else
                {
                    if( ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
                    {
                        IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

                        if( _IotMqtt_DecrementOperationReferences( pOperation, false ) == true )
                        {
                            IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
                            _IotMqtt_DestroyOperation( pOperation );

                            return;
                        }
                        else
                        {
                            /* Operation must be linked. */
                            IotMqtt_Assert( IotLink_IsLinked( &( pOperation->link ) ) );

                            IotListDouble_Remove( &( pOperation->link ) );
                            IotListDouble_InsertHead( &( pMqttConnection->pendingResponse ),
                                                      &( pOperation->link ) );

                            IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
                        }
                    }
                    else
                    {
                        if( pOperation->notify.callback.function == NULL )
                        {
                            pOperation->status = IOT_MQTT_SUCCESS;
                        }
                        else
                        {
                            IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

                            /* Operation must be linked. */
                            IotMqtt_Assert( IotLink_IsLinked( &( pOperation->link ) ) );

                            IotListDouble_Remove( &( pOperation->link ) );
                            IotListDouble_InsertHead( &( pMqttConnection->pendingResponse ),
                                                      &( pOperation->link ) );

                            IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
                        }
                    }
                }
            }
        }
    }

    /* Notify of operation completion if this job set a status. */
    if( pOperation->status != IOT_MQTT_STATUS_PENDING )
    {
        _IotMqtt_Notify( pOperation );
    }
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
    IotLink_t * pResultLink = NULL;
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
    pResultLink = IotListDouble_RemoveFirstMatch( &( pMqttConnection->pendingResponse ),
                                                  NULL,
                                                  _mqttOperation_match,
                                                  &param );
    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* The result will be NULL if no corresponding operation was found in the
     * list. */
    if( pResultLink == NULL )
    {
        IotLogDebug( "In-progress operation %s not found.",
                     IotMqtt_OperationType( operation ) );
    }
    else
    {
        IotLogDebug( "Found in-progress operation %s.",
                     IotMqtt_OperationType( operation ) );

        pResult = IotLink_Container( _mqttOperation_t, pResultLink, link );
    }

    return pResult;
}

/*-----------------------------------------------------------*/

void _IotMqtt_Notify( _mqttOperation_t * const pOperation )
{
    /* Check if operation is waitable. */
    bool waitable = ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE;

    /* Remove any lingering subscriptions if a SUBSCRIBE failed. Rejected
     * subscriptions are removed by the deserializer, so not removed here. */
    if( pOperation->operation == IOT_MQTT_SUBSCRIBE )
    {
        if( ( pOperation->status != IOT_MQTT_SUCCESS ) &&
            ( pOperation->status != IOT_MQTT_SERVER_REFUSED ) )
        {
            _IotMqtt_RemoveSubscriptionByPacket( pOperation->pMqttConnection,
                                                 pOperation->packetIdentifier,
                                                 -1 );
        }
    }

    /* Check if a callback function is set. */
    if( pOperation->notify.callback.function != NULL )
    {
        /* A waitable operation may not have a callback. */
        IotMqtt_Assert( waitable == false );

        /* Non-waitable operation should have job reference of 1. */
        IotMqtt_Assert( pOperation->jobReference == 1 );

        /* Schedule an invocation of the callback. */
        if( _IotMqtt_ScheduleOperation( pOperation,
                                        _IotMqtt_ProcessCompletedOperation ) != IOT_MQTT_SUCCESS )
        {
            IotLogWarn( "Failed to schedule callback job." );
        }
    }
    else
    {
        /* For a waitable operation, post to the wait semaphore. */
        if( waitable == true )
        {
            IotSemaphore_Post( &( pOperation->notify.waitSemaphore ) );
        }

        /* Decrement reference count of operations with no callback. */
        if( _IotMqtt_DecrementOperationReferences( pOperation, false ) == true )
        {
            _IotMqtt_DestroyOperation( pOperation );
        }
    }
}

/*-----------------------------------------------------------*/
