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
 * @brief Calculate the timeout and period of the next PUBLISH retry event.
 *
 * Calculates the next time a PUBLISH should be transmitted and places the
 * retry event in a timer event queue.
 *
 * @param[in] pMqttConnection The MQTT connection associated with the PUBLISH.
 * @param[in] pPublishRetry The current PUBLISH retry event.
 *
 * @return true if the retry event was successfully placed in a timer event queue;
 * false otherwise.
 */
static bool _calculateNextPublishRetry( _mqttConnection_t * const pMqttConnection,
                                        _mqttTimerEvent_t * const pPublishRetry );

/**
 * @brief Send the packet associated with an MQTT operation.
 *
 * Transmits the MQTT packet from a pending operation to the MQTT server, then
 * places the operation in the list of MQTT operations awaiting responses from
 * the server.
 *
 * @param[in] pOperation The MQTT operation with the packet to send.
 */
static void _invokeSend( _mqttOperation_t * const pOperation );

/**
 * @brief Invoke user-provided callback functions.
 *
 * Invokes callback functions associated with either a completed MQTT operation
 * or an incoming PUBLISH message.
 *
 * @param[in] pOperation The MQTT operation with the callback to invoke.
 */
static void _invokeCallback( _mqttOperation_t * const pOperation );

/**
 * @brief Process an MQTT operation.
 *
 * This function is a thread routine that either sends an MQTT packet for
 * in-progress operations, notifies of an operation's completion, or notifies
 * of an incoming PUBLISH message.
 *
 * @param[in] pArgument The address of either #_IotMqttCallback (to invoke a user
 * callback) or #_IotMqttSend (to send an MQTT packet).
 */
static void _processOperation( void * pArgument );

/*-----------------------------------------------------------*/

/**
 * Queues of MQTT operations waiting to be processed.
 */
_mqttOperationQueue_t _IotMqttCallback; /**< @brief Queue of MQTT operations waiting for their callback to be invoked. */
_mqttOperationQueue_t _IotMqttSend;     /**< @brief Queue of MQTT operations waiting to be sent. */
IotMutex_t _IotMqttQueueMutex;          /**< @brief Protects both #_IotMqttSend and #_IotMqttCallback from concurrent access. */

/* List of MQTT operations awaiting a network response. */
IotListDouble_t _IotMqttPendingResponse; /**< @brief List of MQTT operations awaiting a response from the MQTT server. */
IotMutex_t _IotMqttPendingResponseMutex; /**< @brief Protects #_IotMqttPendingResponse from concurrent access. */

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

static bool _calculateNextPublishRetry( _mqttConnection_t * const pMqttConnection,
                                        _mqttTimerEvent_t * const pPublishRetry )
{
    bool status = true;
    _mqttTimerEvent_t * pTimerListHead = NULL;

    /* Check arguments. */
    IotMqtt_Assert( pPublishRetry->pOperation->operation == IOT_MQTT_PUBLISH_TO_SERVER );
    IotMqtt_Assert( pPublishRetry->retry.limit > 0 );
    IotMqtt_Assert( pPublishRetry->retry.nextPeriod <= IOT_MQTT_RETRY_MS_CEILING );

    /* Increment the number of retries. */
    pPublishRetry->retry.count++;

    /* Calculate when the PUBLISH retry event should expire relative to the current
     * time. */
    pPublishRetry->expirationTime = IotClock_GetTimeMs();

    if( pPublishRetry->retry.count > pPublishRetry->retry.limit )
    {
        /* Retry limit reached. Check for a response shortly. */
        pPublishRetry->expirationTime += IOT_MQTT_RESPONSE_WAIT_MS;
    }
    else
    {
        /* Expire at the next retry period. */
        pPublishRetry->expirationTime += pPublishRetry->retry.nextPeriod;

        /* Calculate the next retry period. PUBLISH retries use a truncated exponential
         * backoff strategy. */
        if( pPublishRetry->retry.nextPeriod < IOT_MQTT_RETRY_MS_CEILING )
        {
            pPublishRetry->retry.nextPeriod *= 2;

            if( pPublishRetry->retry.nextPeriod > IOT_MQTT_RETRY_MS_CEILING )
            {
                pPublishRetry->retry.nextPeriod = IOT_MQTT_RETRY_MS_CEILING;
            }
        }
    }

    /* Lock the connection timer mutex to block the timer thread. */
    IotMutex_Lock( &( pMqttConnection->timerMutex ) );

    /* Peek the current head of the timer event list. If the PUBLISH retry expires
     * sooner, re-arm the timer to expire at the PUBLISH retry's expiration time. */
    pTimerListHead = IotLink_Container( _mqttTimerEvent_t,
                                        IotListDouble_PeekHead( &( pMqttConnection->timerEventList ) ),
                                        link );

    if( ( pTimerListHead == NULL ) ||
        ( pTimerListHead->expirationTime > pPublishRetry->expirationTime ) )
    {
        status = IotClock_TimerArm( &( pMqttConnection->timer ),
                                    pPublishRetry->expirationTime - IotClock_GetTimeMs(),
                                    0 );

        if( status == false )
        {
            IotLogError( "Failed to re-arm timer for connection %p.", pMqttConnection );
        }
    }

    /* Insert the PUBLISH retry into the timer event list only if the timer
     * is guaranteed to expire before its expiration time. */
    if( status == true )
    {
        IotListDouble_InsertSorted( &( pMqttConnection->timerEventList ),
                                    &( pPublishRetry->link ),
                                    _IotMqtt_TimerEventCompare );
    }

    IotMutex_Unlock( &( pMqttConnection->timerMutex ) );

    return status;
}

/*-----------------------------------------------------------*/

static void _invokeSend( _mqttOperation_t * const pOperation )
{
    bool waitableOperation = false;

    IotLogDebug( "Operation %s received from queue. Sending data over network.",
                 IotMqtt_OperationType( pOperation->operation ) );

    /* Check if this is a waitable operation. */
    waitableOperation = ( ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE )
                          == IOT_MQTT_FLAG_WAITABLE );

    /* Transmit the MQTT packet from the operation over the network. */
    if( pOperation->pMqttConnection->network.send( pOperation->pMqttConnection->network.pSendContext,
                                                   pOperation->pMqttPacket,
                                                   pOperation->packetSize ) != pOperation->packetSize )
    {
        /* Transmission failed. */
        IotLogError( "Failed to send data for operation %s.",
                     IotMqtt_OperationType( pOperation->operation ) );

        pOperation->status = IOT_MQTT_SEND_ERROR;
    }
    else
    {
        /* DISCONNECT operations are considered successful upon successful
         * transmission. */
        if( pOperation->operation == IOT_MQTT_DISCONNECT )
        {
            pOperation->status = IOT_MQTT_SUCCESS;
        }
        /* Calculate the details of the next PUBLISH retry event. */
        else if( pOperation->pPublishRetry != NULL )
        {
            /* Only a PUBLISH may have a retry event. */
            IotMqtt_Assert( pOperation->operation == IOT_MQTT_PUBLISH_TO_SERVER );

            if( _calculateNextPublishRetry( pOperation->pMqttConnection,
                                            pOperation->pPublishRetry ) == false )
            {
                /* PUBLISH retry failed to re-arm connection timer. Retransmission
                 * will not be sent. */
                pOperation->status = IOT_MQTT_SEND_ERROR;
            }
        }
    }

    /* Once the MQTT packet has been sent, it may be freed if it will not be
     * retransmitted and it's not a PINGREQ. Additionally, the entire operation
     * may be destroyed if no notification method is set. */
    if( ( pOperation->pPublishRetry == NULL ) &&
        ( pOperation->operation != IOT_MQTT_PINGREQ ) )
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
        pOperation->pMqttPacket = NULL;

        if( ( waitableOperation == false ) &&
            ( pOperation->notify.callback.function == NULL ) )
        {
            _IotMqtt_DestroyOperation( pOperation );

            return;
        }
    }

    /* If a status was set by this function, notify of completion. */
    if( pOperation->status != IOT_MQTT_STATUS_PENDING )
    {
        _IotMqtt_Notify( pOperation );
    }
    /* Otherwise, add operation to the list of MQTT operations pending responses. */
    else
    {
        IotMutex_Lock( &( _IotMqttPendingResponseMutex ) );
        IotListDouble_InsertTail( &( _IotMqttPendingResponse ), &( pOperation->link ) );
        IotMutex_Unlock( &( _IotMqttPendingResponseMutex ) );
    }

    /* Notify a waitable operation that it has been sent. */
    if( waitableOperation == true )
    {
        IotSemaphore_Post( &( pOperation->notify.waitSemaphore ) );
    }
}

/*-----------------------------------------------------------*/

static void _invokeCallback( _mqttOperation_t * const pOperation )
{
    _mqttOperation_t * i = NULL, * pCurrent = NULL;
    IotMqttCallbackParam_t callbackParam = { .operation = { 0 } };

    if( pOperation->incomingPublish == true )
    {
        /* Set the pointer to the first PUBLISH. */
        i = pOperation;

        /* Process each PUBLISH in the operation. */
        while( i != NULL )
        {
            /* Save a pointer to the current PUBLISH and move the iterating
             * pointer. */
            pCurrent = i;
            i = i->pNextPublish;

            /* Process the current PUBLISH. */
            if( ( pCurrent->publishInfo.pPayload != NULL ) &&
                ( pCurrent->publishInfo.pTopicName != NULL ) )
            {
                callbackParam.message.info = pCurrent->publishInfo;

                _IotMqtt_ProcessPublish( pCurrent->pMqttConnection,
                                         &callbackParam );
            }

            /* Free any buffers associated with the current PUBLISH message. */
            if( pCurrent->freeReceivedData != NULL )
            {
                IotMqtt_Assert( pCurrent->freeReceivedData != NULL );
                pCurrent->freeReceivedData( ( void * ) pCurrent->pReceivedData );
            }

            /* Free the current PUBLISH. */
            IotMqtt_FreeOperation( pCurrent );
        }
    }
    else
    {
        /* Operations with no callback should not have been passed. */
        IotMqtt_Assert( pOperation->notify.callback.function != NULL );

        IotLogDebug( "Operation %s received from queue. Invoking user callback.",
                     IotMqtt_OperationType( pOperation->operation ) );

        /* Set callback parameters. */
        callbackParam.mqttConnection = pOperation->pMqttConnection;
        callbackParam.operation.type = pOperation->operation;
        callbackParam.operation.reference = pOperation;
        callbackParam.operation.result = pOperation->status;

        /* Invoke user callback function. */
        pOperation->notify.callback.function( pOperation->notify.callback.param1,
                                              &callbackParam );

        /* Once the user-provided callback returns, the operation can be destroyed. */
        _IotMqtt_DestroyOperation( pOperation );
    }
}

/*-----------------------------------------------------------*/

static void _processOperation( void * pArgument )
{
    _mqttOperation_t * pOperation = NULL;
    _mqttOperationQueue_t * pQueue = ( _mqttOperationQueue_t * ) pArgument;

    /* There are only two valid values for this function's argument. */
    IotMqtt_Assert( ( pQueue == &( _IotMqttCallback ) ) ||
                    ( pQueue == &( _IotMqttSend ) ) );

    IotLogDebug( "New thread for processing MQTT operations started." );

    while( true )
    {
        IotLogDebug( "Removing oldest operation from MQTT pending operations." );

        /* Remove the oldest operation from the queue of pending MQTT operations. */
        IotMutex_Lock( &( _IotMqttQueueMutex ) );

        pOperation = IotLink_Container( _mqttOperation_t,
                                        IotQueue_Dequeue( &( pQueue->queue ) ),
                                        link );

        /* If no operation was received, this thread will terminate. Increment
         * number of available threads. */
        if( pOperation == NULL )
        {
            IotSemaphore_Post( &( pQueue->availableThreads ) );
        }

        IotMutex_Unlock( &( _IotMqttQueueMutex ) );

        /* Terminate thread if no operation was received. */
        if( pOperation == NULL )
        {
            break;
        }

        /* Run thread routine based on given queue. */
        if( pQueue == &( _IotMqttCallback ) )
        {
            /* Only incoming PUBLISH messages and completed operations should invoke
             * the callback routine. */
            IotMqtt_Assert( ( pOperation->incomingPublish == true ) ||
                            ( pOperation->status != IOT_MQTT_STATUS_PENDING ) );

            _invokeCallback( pOperation );
        }
        else
        {
            /* Only operations with an allocated packet should be sent. */
            IotMqtt_Assert( pOperation->status == IOT_MQTT_STATUS_PENDING );
            IotMqtt_Assert( pOperation->pMqttPacket != NULL );
            IotMqtt_Assert( pOperation->packetSize != 0 );

            _invokeSend( pOperation );
        }
    }

    IotLogDebug( "No more pending operations. Terminating MQTT processing thread." );
}

/*-----------------------------------------------------------*/

int _IotMqtt_TimerEventCompare( const IotLink_t * const pTimerEventLink1,
                                const IotLink_t * const pTimerEventLink2 )
{
    const _mqttTimerEvent_t * pTimerEvent1 = IotLink_Container( _mqttTimerEvent_t,
                                                                pTimerEventLink1,
                                                                link );
    const _mqttTimerEvent_t * pTimerEvent2 = IotLink_Container( _mqttTimerEvent_t,
                                                                pTimerEventLink2,
                                                                link );

    if( pTimerEvent1->expirationTime < pTimerEvent2->expirationTime )
    {
        return -1;
    }

    if( pTimerEvent1->expirationTime > pTimerEvent2->expirationTime )
    {
        return 1;
    }

    return 0;
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

    /* Check if this operation is a PUBLISH. Clean up its retry event if
     * necessary. */
    if( ( pOperation->operation == IOT_MQTT_PUBLISH_TO_SERVER ) &&
        ( pOperation->pPublishRetry != NULL ) )
    {
        IotMutex_Lock( &( pOperation->pMqttConnection->timerMutex ) );

        /* Remove the timer event from the timer event list before freeing it.
         * The return value of this function is not checked because it always
         * equals the publish retry event or is NULL. */
        ( void ) IotListDouble_RemoveFirstMatch( &( pOperation->pMqttConnection->timerEventList ),
                                                 NULL,
                                                 NULL,
                                                 pOperation->pPublishRetry );

        IotMutex_Unlock( &( pOperation->pMqttConnection->timerMutex ) );

        IotMqtt_FreeTimerEvent( pOperation->pPublishRetry );
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

IotMqttError_t _IotMqtt_EnqueueOperation( _mqttOperation_t * const pOperation,
                                          _mqttOperationQueue_t * const pQueue )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* The given operation must not already be queued. */
    IotMqtt_Assert( IotLink_IsLinked( &( pOperation->link ) ) == false );

    /* Check that the queue argument is either the callback queue or send queue. */
    IotMqtt_Assert( ( pQueue == &( _IotMqttCallback ) ) ||
                    ( pQueue == &( _IotMqttSend ) ) );

    /* Lock mutex for exclusive access to queues. */
    IotMutex_Lock( &( _IotMqttQueueMutex ) );

    /* Add operation to queue. */
    IotQueue_Enqueue( &( pQueue->queue ), &( pOperation->link ) );

    /* Check if a new thread can be created. */
    if( IotSemaphore_TryWait( &( pQueue->availableThreads ) ) == true )
    {
        /* Create new thread. */
        if( Iot_CreateDetachedThread( _processOperation,
                                      pQueue,
                                      IOT_THREAD_DEFAULT_PRIORITY,
                                      IOT_THREAD_DEFAULT_STACK_SIZE ) == false )
        {
            /* New thread could not be created. Remove enqueued operation and
             * report error. */
            IotQueue_Remove( &( pOperation->link ) );
            IotSemaphore_Post( &( pQueue->availableThreads ) );
            status = IOT_MQTT_NO_MEMORY;
        }
    }

    IotMutex_Unlock( &( _IotMqttQueueMutex ) );

    return status;
}

/*-----------------------------------------------------------*/

_mqttOperation_t * _IotMqtt_FindOperation( IotMqttOperationType_t operation,
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
    IotMutex_Lock( &( _IotMqttPendingResponseMutex ) );
    pResult = IotLink_Container( _mqttOperation_t,
                                 IotListDouble_RemoveFirstMatch( &( _IotMqttPendingResponse ),
                                                                 NULL,
                                                                 _mqttOperation_match,
                                                                 &param ),
                                 link );
    IotMutex_Unlock( &( _IotMqttPendingResponseMutex ) );

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
            if( _IotMqtt_EnqueueOperation( pOperation,
                                           &( _IotMqttCallback ) ) != IOT_MQTT_SUCCESS )
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
