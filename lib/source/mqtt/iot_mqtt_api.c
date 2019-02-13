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
 * @file iot_mqtt_api.c
 * @brief Implements most user-facing functions of the MQTT library.
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

/* Validate MQTT configuration settings. */
#if IOT_MQTT_ENABLE_ASSERTS != 0 && IOT_MQTT_ENABLE_ASSERTS != 1
    #error "IOT_MQTT_ENABLE_ASSERTS must be 0 or 1."
#endif
#if IOT_MQTT_ENABLE_METRICS != 0 && IOT_MQTT_ENABLE_METRICS != 1
    #error "IOT_MQTT_ENABLE_METRICS must be 0 or 1."
#endif
#if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES != 0 && IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES != 1
    #error "IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES must be 0 or 1."
#endif
#if IOT_MQTT_MAX_CALLBACK_THREADS <= 0
    #error "IOT_MQTT_MAX_CALLBACK_THREADS cannot be 0 or negative."
#endif
#if IOT_MQTT_MAX_SEND_THREADS <= 0
    #error "IOT_MQTT_MAX_SEND_THREADS cannot be 0 or negative."
#endif
#if IOT_MQTT_TEST != 0 && IOT_MQTT_TEST != 1
    #error "IOT_MQTT_MQTT_TEST must be 0 or 1."
#endif
#if IOT_MQTT_RESPONSE_WAIT_MS <= 0
    #error "IOT_MQTT_RESPONSE_WAIT_MS cannot be 0 or negative."
#endif
#if IOT_MQTT_RETRY_MS_CEILING <= 0
    #error "IOT_MQTT_RETRY_MS_CEILING cannot be 0 or negative."
#endif
#if IOT_MQTT_TIMER_EVENT_THRESHOLD_MS <= 0
    #error "IOT_MQTT_TIMER_EVENT_THRESHOLD_MS cannot be 0 or negative."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Determines if an MQTT subscription is safe to remove based on its
 * reference count.
 *
 * @param[in] pSubscriptionLink Pointer to the link member of an #_mqttSubscription_t.
 * @param[in] pMatch Not used.
 *
 * @return `true` if the given subscription has no references; `false` otherwise.
 */
static bool _mqttSubscription_shouldRemove( const IotLink_t * pSubscriptionLink,
                                            void * pMatch );

/**
 * @brief Creates a new MQTT connection and initializes its members.
 *
 * @param[in] awsIotMqttMode Specifies if this connection is to an AWS IoT MQTT server.
 * @param[in] pNetworkInterface User-provided network interface for the new
 * connection.
 * @param[in] keepAliveSeconds User-provided keep-alive interval for the new connection.
 *
 * @return Pointer to a newly-allocated MQTT connection on success; `NULL` on
 * failure.
 */
static _mqttConnection_t * _createMqttConnection( bool awsIotMqttMode,
                                                  const IotMqttNetIf_t * const pNetworkInterface,
                                                  uint16_t keepAliveSeconds );

/**
 * @brief Destroys the members of an MQTT connection.
 *
 * @param[in] pMqttConnection Which connection to destroy.
 */
static void _destroyMqttConnection( _mqttConnection_t * const pMqttConnection );

/**
 * @brief The common component of both @ref mqtt_function_subscribe and @ref
 * mqtt_function_unsubscribe.
 *
 * See @ref mqtt_function_subscribe or @ref mqtt_function_unsubscribe for a
 * description of the parameters and return values.
 */
static IotMqttError_t _subscriptionCommon( IotMqttOperationType_t operation,
                                           IotMqttConnection_t mqttConnection,
                                           const IotMqttSubscription_t * const pSubscriptionList,
                                           size_t subscriptionCount,
                                           uint32_t flags,
                                           const IotMqttCallbackInfo_t * const pCallbackInfo,
                                           IotMqttReference_t * const pSubscriptionRef );

/*-----------------------------------------------------------*/

/**
 * @brief Ensures that only one CONNECT operation is in-progress at any time.
 *
 * Because CONNACK contains no data about which CONNECT packet it acknowledges,
 * only one CONNECT operation may be in-progress at any time.
 */
static IotMutex_t _connectMutex;

/*-----------------------------------------------------------*/

static bool _mqttSubscription_shouldRemove( const IotLink_t * pSubscriptionLink,
                                            void * pMatch )
{
    bool match = false;
    _mqttSubscription_t * pSubscription = IotLink_Container( _mqttSubscription_t,
                                                             pSubscriptionLink,
                                                             link );

    /* Silence warnings about unused parameters. */
    ( void ) pMatch;

    /* Reference count must not be negative. */
    IotMqtt_Assert( pSubscription->references >= 0 );

    /* Check if any subscription callbacks are using this subscription. */
    if( pSubscription->references > 0 )
    {
        /* Set the unsubscribed flag, but do not remove the subscription yet. */
        pSubscription->unsubscribed = true;
    }
    else
    {
        /* No references for this subscription; it can be removed. */
        match = true;
    }

    return match;
}

/*-----------------------------------------------------------*/

static _mqttConnection_t * _createMqttConnection( bool awsIotMqttMode,
                                                  const IotMqttNetIf_t * const pNetworkInterface,
                                                  uint16_t keepAliveSeconds )
{
    _mqttConnection_t * pNewMqttConnection = NULL;

    /* AWS IoT service limits set minimum and maximum values for keep-alive interval.
     * Adjust the user-provided keep-alive interval based on these requirements. */
    if( awsIotMqttMode == true )
    {
        if( keepAliveSeconds < _AWS_IOT_MQTT_SERVER_MIN_KEEPALIVE )
        {
            keepAliveSeconds = _AWS_IOT_MQTT_SERVER_MIN_KEEPALIVE;
        }
        else if( ( keepAliveSeconds > _AWS_IOT_MQTT_SERVER_MAX_KEEPALIVE ) || ( keepAliveSeconds == 0 ) )
        {
            keepAliveSeconds = _AWS_IOT_MQTT_SERVER_MAX_KEEPALIVE;
        }
    }

    /* Allocate memory to store data for the new MQTT connection. */
    pNewMqttConnection = ( _mqttConnection_t * )
                         IotMqtt_MallocConnection( sizeof( _mqttConnection_t ) );

    if( pNewMqttConnection == NULL )
    {
        IotLogError( "Failed to allocate memory for new MQTT connection." );
        goto errorMallocConnection;
    }

    /* Clear the MQTT connection, then copy the MQTT server mode and network
     * interface. */
    ( void ) memset( pNewMqttConnection, 0x00, sizeof( _mqttConnection_t ) );
    pNewMqttConnection->awsIotMqttMode = awsIotMqttMode;
    pNewMqttConnection->network = *pNetworkInterface;

    /* Create the references mutex for a new connection. */
    if( IotMutex_Create( &( pNewMqttConnection->referencesMutex ), false ) == false )
    {
        IotLogError( "Failed to create references mutex for new connection." );
        goto errorReferencesMutex;
    }

    /* Create the subscription mutex for a new connection. */
    if( IotMutex_Create( &( pNewMqttConnection->subscriptionMutex ), false ) == false )
    {
        IotLogError( "Failed to create subscription mutex for new connection." );
        goto errorSubscriptionMutex;
    }

    /* Create the new connection's subscription and operation lists. */
    IotListDouble_Create( &( pNewMqttConnection->subscriptionList ) );
    IotListDouble_Create( &( pNewMqttConnection->pendingProcessing ) );
    IotListDouble_Create( &( pNewMqttConnection->pendingResponse ) );

    /* Check if keep-alive is active for this connection. */
    if( keepAliveSeconds != 0 )
    {
        /* Convert the keep-alive interval to milliseconds. */
        pNewMqttConnection->keepAliveMs = keepAliveSeconds * 1000;

        /* Choose a PINGREQ serializer function. */
        IotMqttError_t ( * serializePingreq )( uint8_t ** const,
                                               size_t * const ) = _IotMqtt_SerializePingreq;

        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pNewMqttConnection->network.serialize.pingreq != NULL )
            {
                serializePingreq = pNewMqttConnection->network.serialize.pingreq;
            }
        #endif

        if( serializePingreq( &( pNewMqttConnection->pPingreqPacket ),
                              &( pNewMqttConnection->pingreqPacketSize ) ) != IOT_MQTT_SUCCESS )
        {
            IotLogError( "Failed to allocate PINGREQ packet for new connection." );
            goto errorSerializePingreq;
        }

        /* Create the task pool job that processes keep-alive. */
        if( IotTaskPool_CreateJob( _IotMqtt_ProcessKeepAlive,
                                   pNewMqttConnection,
                                   &( pNewMqttConnection->keepAliveJob ) ) != IOT_TASKPOOL_SUCCESS )
        {
            IotLogError( "Failed to create keep-alive job for new connection." );

            /* Keep alive job creation should never fail when valid parameters
             * are given. Abort the program on failure. */
            IotMqtt_Assert( false );
        }
    }

    return pNewMqttConnection;

errorSerializePingreq: IotMutex_Destroy( &( pNewMqttConnection->subscriptionMutex ) );
errorSubscriptionMutex: IotMutex_Destroy( &( pNewMqttConnection->referencesMutex ) );
errorReferencesMutex: IotMqtt_FreeConnection( pNewMqttConnection );
errorMallocConnection: return NULL;
}

/*-----------------------------------------------------------*/

static void _destroyMqttConnection( _mqttConnection_t * const pMqttConnection )
{
    /* Stop the keep-alive routine. */
    if( pMqttConnection->keepAliveMs != 0 )
    {
        /* A PINGREQ packet must be allocated. */
        IotMqtt_Assert( pMqttConnection->pPingreqPacket != NULL );
        IotMqtt_Assert( pMqttConnection->pingreqPacketSize != 0 );

        _IotMqtt_FreePacket( pMqttConnection->pPingreqPacket );
    }

    /* Remove all subscriptions. */
    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );
    IotListDouble_RemoveAllMatches( &( pMqttConnection->subscriptionList ),
                                    _mqttSubscription_shouldRemove,
                                    NULL,
                                    IotMqtt_FreeSubscription,
                                    offsetof( _mqttSubscription_t, link ) );
    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

    /* Destroy mutexes and free connection. */
    IotMutex_Destroy( &( pMqttConnection->referencesMutex ) );
    IotMutex_Destroy( &( pMqttConnection->subscriptionMutex ) );
    IotMqtt_FreeConnection( pMqttConnection );
}

/*-----------------------------------------------------------*/

static IotMqttError_t _subscriptionCommon( IotMqttOperationType_t operation,
                                           IotMqttConnection_t mqttConnection,
                                           const IotMqttSubscription_t * const pSubscriptionList,
                                           size_t subscriptionCount,
                                           uint32_t flags,
                                           const IotMqttCallbackInfo_t * const pCallbackInfo,
                                           IotMqttReference_t * const pSubscriptionRef )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pSubscriptionOperation = NULL;
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) mqttConnection;

    /* Subscription serializer function. */
    IotMqttError_t ( * serializeSubscription )( const IotMqttSubscription_t * const,
                                                size_t,
                                                uint8_t ** const,
                                                size_t * const,
                                                uint16_t * const ) = NULL;

    /* This function should only be called for subscribe or unsubscribe. */
    IotMqtt_Assert( ( operation == IOT_MQTT_SUBSCRIBE ) ||
                    ( operation == IOT_MQTT_UNSUBSCRIBE ) );

    /* Check that all elements in the subscription list are valid. */
    _validateParameter( _IotMqtt_ValidateSubscriptionList( operation,
                                                           pMqttConnection->awsIotMqttMode,
                                                           pSubscriptionList,
                                                           subscriptionCount ) == true,
                        NULL );

    /* Check that a reference pointer is provided for a waitable operation. */
    if( ( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE ) &&
        ( pSubscriptionRef == NULL ) )
    {
        _validateParameter( pSubscriptionRef != NULL,
                            "Reference must be provided for a waitable %s.",
                            IotMqtt_OperationType( operation ) );
    }

    /* Choose a subscription serialize function. */
    if( operation == IOT_MQTT_SUBSCRIBE )
    {
        serializeSubscription = _IotMqtt_SerializeSubscribe;

        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pMqttConnection->network.serialize.subscribe != NULL )
            {
                serializeSubscription = pMqttConnection->network.serialize.subscribe;
            }
        #endif
    }
    else
    {
        serializeSubscription = _IotMqtt_SerializeUnsubscribe;

        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pMqttConnection->network.serialize.unsubscribe != NULL )
            {
                serializeSubscription = pMqttConnection->network.serialize.unsubscribe;
            }
        #endif
    }

    /* Remove the MQTT subscription list for an UNSUBSCRIBE. */
    if( operation == IOT_MQTT_UNSUBSCRIBE )
    {
        _IotMqtt_RemoveSubscriptionByTopicFilter( pMqttConnection,
                                                  pSubscriptionList,
                                                  subscriptionCount );
    }

    /* Create a subscription operation. */
    status = _IotMqtt_CreateOperation( &pSubscriptionOperation,
                                       flags,
                                       pCallbackInfo );

    if( status != IOT_MQTT_SUCCESS )
    {
        return status;
    }

    /* Check the subscription operation data and set the remaining members. */
    IotMqtt_Assert( pSubscriptionOperation->status == IOT_MQTT_STATUS_PENDING );
    IotMqtt_Assert( pSubscriptionOperation->retry.limit == 0 );
    pSubscriptionOperation->operation = operation;
    pSubscriptionOperation->pMqttConnection = pMqttConnection;

    /* Generate a subscription packet from the subscription list. */
    status = serializeSubscription( pSubscriptionList,
                                    subscriptionCount,
                                    &( pSubscriptionOperation->pMqttPacket ),
                                    &( pSubscriptionOperation->packetSize ),
                                    &( pSubscriptionOperation->packetIdentifier ) );

    if( status != IOT_MQTT_SUCCESS )
    {
        _IotMqtt_DestroyOperation( pSubscriptionOperation );

        return status;
    }

    /* Check the serialized MQTT packet. */
    IotMqtt_Assert( pSubscriptionOperation->pMqttPacket != NULL );
    IotMqtt_Assert( pSubscriptionOperation->packetSize > 0 );

    /* Add the subscription list for a SUBSCRIBE. */
    if( operation == IOT_MQTT_SUBSCRIBE )
    {
        status = _IotMqtt_AddSubscriptions( pMqttConnection,
                                            pSubscriptionOperation->packetIdentifier,
                                            pSubscriptionList,
                                            subscriptionCount );

        if( status != IOT_MQTT_SUCCESS )
        {
            _IotMqtt_DestroyOperation( pSubscriptionOperation );

            return status;
        }
    }

    /* Set the reference, if provided. This must be set before the subscription
     * is pushed to the network queue to avoid a race condition. */
    if( pSubscriptionRef != NULL )
    {
        *pSubscriptionRef = pSubscriptionOperation;
    }

    /* Schedule the subscription operation for network transmission. */
    if( _IotMqtt_ScheduleOperation( pSubscriptionOperation,
                                    _IotMqtt_ProcessSend ) != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to schedule %s for sending.",
                     IotMqtt_OperationType( operation ) );

        if( operation == IOT_MQTT_SUBSCRIBE )
        {
            _IotMqtt_RemoveSubscriptionByPacket( pMqttConnection,
                                                 pSubscriptionOperation->packetIdentifier,
                                                 -1 );
        }

        _IotMqtt_DestroyOperation( pSubscriptionOperation );

        /* Clear the previously set (and now invalid) reference. */
        if( pSubscriptionRef != NULL )
        {
            *pSubscriptionRef = IOT_MQTT_REFERENCE_INITIALIZER;
        }

        return IOT_MQTT_SCHEDULING_ERROR;
    }

    IotLogInfo( "MQTT %s operation scheduled.",
                IotMqtt_OperationType( operation ) );

    /* The subscription operation is waiting for a network response. */
    return IOT_MQTT_STATUS_PENDING;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_IncrementConnectionReferences( _mqttConnection_t * const pMqttConnection )
{
    bool disconnected = false;

    /* Lock the mutex protecting the reference count. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    /* Reference count must not be negative. */
    IotMqtt_Assert( pMqttConnection->references >= 0 );

    /* Read connection status. */
    disconnected = pMqttConnection->disconnected;

    /* Increment the connection's reference count if it is not disconnected. */
    if( disconnected == false )
    {
        ( pMqttConnection->references )++;
        IotLogDebug( "Reference count for MQTT connection %p changed from %ld to %ld.",
                     pMqttConnection,
                     ( long int ) pMqttConnection->references - 1,
                     ( long int ) pMqttConnection->references );
    }
    else
    {
        IotLogWarn( "Attempt to use closed MQTT connection %p.", pMqttConnection );
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    return( disconnected == false );
}

/*-----------------------------------------------------------*/

void _IotMqtt_DecrementConnectionReferences( _mqttConnection_t * const pMqttConnection )
{
    bool destroyConnection = false;

    /* Lock the mutex protecting the reference count. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    /* Decrement reference count. It must not be negative. */
    ( pMqttConnection->references )--;
    IotMqtt_Assert( pMqttConnection->references >= 0 );

    /* Check if this connection may be destroyed. */
    if( pMqttConnection->disconnected == true )
    {
        if( pMqttConnection->references == 0 )
        {
            destroyConnection = true;
        }
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Destroy an unreferenced MQTT connection. */
    if( destroyConnection == true )
    {
        _destroyMqttConnection( pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Init( void )
{
    const IotTaskPoolInfo_t taskPoolInfo = IOT_TASKPOOL_INFO_INITIALIZER_MEDIUM;

    if( IotTaskPool_Create( &taskPoolInfo, &_IotMqttTaskPool) != IOT_TASKPOOL_SUCCESS )
    {
        IotLogError( "Failed to initialize MQTT library task pool." );
        goto errorTaskPool;
    }

    /* Create CONNECT mutex. */
    if( IotMutex_Create( &( _connectMutex ), false ) == false )
    {
        IotLogError( "Failed to initialize MQTT library connect mutex." );
        goto errorConnectMutex;
    }

    /* Initialize MQTT serializer. */
    if( _IotMqtt_InitSerialize() != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to initialize MQTT library serializer. " );
        goto errorInitSerialize;
    }

    IotLogInfo( "MQTT library successfully initialized." );

    return IOT_MQTT_SUCCESS;

errorInitSerialize: IotMutex_Destroy( &( _connectMutex ) );
errorConnectMutex: IotTaskPool_Destroy( &_IotMqttTaskPool );
errorTaskPool: return IOT_MQTT_INIT_FAILED;
}

/*-----------------------------------------------------------*/

void IotMqtt_Cleanup()
{
    /* Clean up MQTT serializer. */
    _IotMqtt_CleanupSerialize();

    /* Clean up CONNECT mutex. */
    IotMutex_Destroy( &( _connectMutex ) );

    /* Clean up MQTT library task pool. */
    IotTaskPool_Destroy( &_IotMqttTaskPool );

    IotLogInfo( "MQTT library cleanup done." );
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Connect( IotMqttConnection_t * pMqttConnection,
                                const IotMqttNetIf_t * const pNetworkInterface,
                                const IotMqttConnectInfo_t * const pConnectInfo,
                                uint64_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttConnection_t * pNewMqttConnection = NULL;
    _mqttOperation_t * pConnectOperation = NULL;

    /* Default CONNECT serializer function. */
    IotMqttError_t ( * serializeConnect )( const IotMqttConnectInfo_t * const,
                                           uint8_t ** const,
                                           size_t * const ) = _IotMqtt_SerializeConnect;

    /* Validate network interface and connect info. */
    _validateParameter( _IotMqtt_ValidateNetIf( pNetworkInterface ) == true, NULL );
    _validateParameter( _IotMqtt_ValidateConnect( pConnectInfo ) == true, NULL );

    /* If will info is provided, check that it is valid. */
    if( pConnectInfo->pWillInfo != NULL )
    {
        _validateParameter( _IotMqtt_ValidatePublish( pConnectInfo->awsIotMqttMode,
                                                      pConnectInfo->pWillInfo ) == true,
                            NULL );

        /* Will message payloads cannot be larger than 65535. This restriction
         * applies only to will messages, and not normal PUBLISH messages. */
        _validateParameter( pConnectInfo->pWillInfo->payloadLength <= UINT16_MAX,
                            "Will payload cannot be larger than 65535." );
    }

    /* If previous subscriptions are provided, check that they are valid. */
    if( pConnectInfo->cleanSession == false )
    {
        if( pConnectInfo->pPreviousSubscriptions != NULL )
        {
            _validateParameter( _IotMqtt_ValidateSubscriptionList( IOT_MQTT_SUBSCRIBE,
                                                                   pConnectInfo->awsIotMqttMode,
                                                                   pConnectInfo->pPreviousSubscriptions,
                                                                   pConnectInfo->previousSubscriptionCount ) == true,
                                NULL );
        }
    }

    /* Choose a CONNECT serializer function. */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pNetworkInterface->serialize.connect != NULL )
        {
            serializeConnect = pNetworkInterface->serialize.connect;
        }
    #endif

    IotLogInfo( "Establishing new MQTT connection." );

    /* Allocate memory to store data for the new MQTT connection. */
    pNewMqttConnection = _createMqttConnection( pConnectInfo->awsIotMqttMode,
                                                pNetworkInterface,
                                                pConnectInfo->keepAliveSeconds );

    if( pNewMqttConnection == NULL )
    {
        status = IOT_MQTT_NO_MEMORY;
        goto errorCreateConnection;
    }

    /* Create a CONNECT operation. */
    status = _IotMqtt_CreateOperation( &pConnectOperation,
                                       IOT_MQTT_FLAG_WAITABLE,
                                       NULL );

    if( status != IOT_MQTT_SUCCESS )
    {
        goto errorCreateOperation;
    }

    /* Ensure the members set by operation creation and serialization
     * are appropriate for a blocking CONNECT. */
    IotMqtt_Assert( pConnectOperation->status == IOT_MQTT_STATUS_PENDING );
    IotMqtt_Assert( ( pConnectOperation->flags & IOT_MQTT_FLAG_WAITABLE )
                    == IOT_MQTT_FLAG_WAITABLE );
    IotMqtt_Assert( pConnectOperation->retry.limit == 0 );

    /* Set the operation type. */
    pConnectOperation->operation = IOT_MQTT_CONNECT;

    /* Set the MQTT connection. */
    pConnectOperation->pMqttConnection = pNewMqttConnection;

    /* Add previous session subscriptions. */
    if( pConnectInfo->pPreviousSubscriptions != NULL )
    {
        /* Previous subscription count should have been validated as nonzero. */
        IotMqtt_Assert( pConnectInfo->previousSubscriptionCount > 0 );

        status = _IotMqtt_AddSubscriptions( pNewMqttConnection,
                                            2,
                                            pConnectInfo->pPreviousSubscriptions,
                                            pConnectInfo->previousSubscriptionCount );

        if( status != IOT_MQTT_SUCCESS )
        {
            goto errorAddSubscriptions;
        }
    }

    /* Convert the connect info and will info objects to an MQTT CONNECT packet. */
    status = serializeConnect( pConnectInfo,
                               &( pConnectOperation->pMqttPacket ),
                               &( pConnectOperation->packetSize ) );

    if( status != IOT_MQTT_SUCCESS )
    {
        goto errorSerializeConnect;
    }

    /* Check the serialized MQTT packet. */
    IotMqtt_Assert( pConnectOperation->pMqttPacket != NULL );
    IotMqtt_Assert( pConnectOperation->packetSize > 0 );

    /* Set the output parameter so it may be used by the network receive callback. */
    *pMqttConnection = pNewMqttConnection;

    /* Prevent another CONNECT operation from using the network. */
    IotMutex_Lock( &_connectMutex );

    /* Add the CONNECT operation to the send queue for network transmission. */
    status = _IotMqtt_ScheduleOperation( pConnectOperation,
                                         _IotMqtt_ProcessSend );

    if( status != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to enqueue CONNECT for sending." );
        _IotMqtt_DestroyOperation( pConnectOperation );
    }
    else
    {
        /* Wait for the CONNECT operation to complete, i.e. wait for CONNACK. */
        status = IotMqtt_Wait( ( IotMqttReference_t ) pConnectOperation,
                               timeoutMs );
    }

    /* Unlock the CONNECT mutex. */
    IotMutex_Unlock( &_connectMutex );

    /* When a connection is successfully established, schedule keep-alive job. */
    if( status == IOT_MQTT_SUCCESS )
    {
        /* Schedule the keep-alive job to run after one keep-alive period. */
        if( pNewMqttConnection->keepAliveMs > 0 )
        {
            IotLogDebug( "Scheduling MQTT keep-alive job." );

            if( IotTaskPool_ScheduleDeferred( &( _IotMqttTaskPool ),
                                              &( pNewMqttConnection->keepAliveJob ),
                                              pNewMqttConnection->keepAliveMs ) != IOT_TASKPOOL_SUCCESS )
            {
                status = IOT_MQTT_SCHEDULING_ERROR;
            }
        }
    }

    /* Check the status of the CONNECT operation. */
    if( status == IOT_MQTT_SUCCESS )
    {
        IotLogInfo( "New MQTT connection %p established.", pNewMqttConnection );
    }
    else
    {
        /* Otherwise, free resources and log an error. */
        _destroyMqttConnection( pNewMqttConnection );
        *pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

        IotLogError( "Failed to establish new MQTT connection, error %s.",
                     IotMqtt_strerror( status ) );
    }

    return status;

errorSerializeConnect:
errorAddSubscriptions: _IotMqtt_DestroyOperation( pConnectOperation );
errorCreateOperation: _destroyMqttConnection( pNewMqttConnection );
errorCreateConnection: return status;
}

/*-----------------------------------------------------------*/

void IotMqtt_Disconnect( IotMqttConnection_t mqttConnection,
                         bool cleanupOnly )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) mqttConnection;
    _mqttOperation_t * pDisconnectOperation = NULL;

    IotLogInfo( "Disconnecting MQTT connection %p.", pMqttConnection );

    /* Purge all of this connection's subscriptions. */
    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );
    IotListDouble_RemoveAllMatches( &( pMqttConnection->subscriptionList ),
                                    _mqttSubscription_shouldRemove,
                                    NULL,
                                    IotMqtt_FreeSubscription,
                                    offsetof( _mqttSubscription_t, link ) );
    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

    /* Only send a DISCONNECT packet if the connection is active and the "cleanup only"
     * option is false. */
    if( ( pMqttConnection->disconnected == false ) && ( cleanupOnly == false ) )
    {
        /* Create a DISCONNECT operation. This function blocks until the DISCONNECT
         * packet is sent, so it sets IOT_MQTT_FLAG_WAITABLE. */
        status = _IotMqtt_CreateOperation( &pDisconnectOperation,
                                           IOT_MQTT_FLAG_WAITABLE,
                                           NULL );

        if( status == IOT_MQTT_SUCCESS )
        {
            /* Ensure that the members set by operation creation and serialization
             * are appropriate for a blocking DISCONNECT. */
            IotMqtt_Assert( pDisconnectOperation->status == IOT_MQTT_STATUS_PENDING );
            IotMqtt_Assert( ( pDisconnectOperation->flags & IOT_MQTT_FLAG_WAITABLE )
                            == IOT_MQTT_FLAG_WAITABLE );
            IotMqtt_Assert( pDisconnectOperation->retry.limit == 0 );

            /* Set the remaining members of the DISCONNECT operation. */
            pDisconnectOperation->operation = IOT_MQTT_DISCONNECT;
            pDisconnectOperation->pMqttConnection = pMqttConnection;

            /* Choose a disconnect serializer. */
            IotMqttError_t ( * serializeDisconnect )( uint8_t ** const,
                                                      size_t * const ) = _IotMqtt_SerializeDisconnect;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->network.serialize.disconnect != NULL )
                {
                    serializeDisconnect = pMqttConnection->network.serialize.disconnect;
                }
            #endif

            /* Generate a DISCONNECT packet. */
            status = serializeDisconnect( &( pDisconnectOperation->pMqttPacket ),
                                          &( pDisconnectOperation->packetSize ) );
        }

        if( status == IOT_MQTT_SUCCESS )
        {
            /* Check the serialized MQTT packet. */
            IotMqtt_Assert( pDisconnectOperation->pMqttPacket != NULL );
            IotMqtt_Assert( pDisconnectOperation->packetSize > 0 );

            /* Schedule the DISCONNECT operation for network transmission. */
            if( _IotMqtt_ScheduleOperation( pDisconnectOperation,
                                            _IotMqtt_ProcessSend ) != IOT_MQTT_SUCCESS )
            {
                IotLogWarn( "Failed to schedule DISCONNECT for sending." );
                _IotMqtt_DestroyOperation( pDisconnectOperation );
            }
            else
            {
                /* Wait until the DISCONNECT packet has been transmitted. DISCONNECT
                 * should always be successful because it does not rely on any incoming
                 * data. */
                status = IotMqtt_Wait( ( IotMqttReference_t ) pDisconnectOperation,
                                       0 );

                /* A wait on DISCONNECT should only ever return SUCCESS or SEND ERROR. */
                IotMqtt_Assert( ( status == IOT_MQTT_SUCCESS ) ||
                                ( status == IOT_MQTT_SEND_ERROR ) );

                IotLogInfo( "MQTT connection %p disconnected.", pMqttConnection );
            }
        }
    }

    /* Close the network connection regardless of whether an MQTT DISCONNECT
     * packet was sent. */
    if( pMqttConnection->network.disconnect != NULL )
    {
        pMqttConnection->network.disconnect( 0, pMqttConnection->network.pDisconnectContext );
    }
    else
    {
        IotLogWarn( "No disconnect function was set. Network connection not closed." );
    }

    /* Destroy the MQTT connection's mutexes. */
    IotMutex_Destroy( &( pMqttConnection->subscriptionMutex ) );

    /* Free the memory used by this connection. */
    IotMqtt_FreeConnection( pMqttConnection );
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Subscribe( IotMqttConnection_t mqttConnection,
                                  const IotMqttSubscription_t * const pSubscriptionList,
                                  size_t subscriptionCount,
                                  uint32_t flags,
                                  const IotMqttCallbackInfo_t * const pCallbackInfo,
                                  IotMqttReference_t * const pSubscribeRef )
{
    return _subscriptionCommon( IOT_MQTT_SUBSCRIBE,
                                mqttConnection,
                                pSubscriptionList,
                                subscriptionCount,
                                flags,
                                pCallbackInfo,
                                pSubscribeRef );
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_TimedSubscribe( IotMqttConnection_t mqttConnection,
                                       const IotMqttSubscription_t * const pSubscriptionList,
                                       size_t subscriptionCount,
                                       uint32_t flags,
                                       uint64_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttReference_t subscribeRef = IOT_MQTT_REFERENCE_INITIALIZER;

    /* Flags are not used, but the parameter is present for future compatibility. */
    ( void ) flags;

    /* Call the asynchronous SUBSCRIBE function. */
    status = IotMqtt_Subscribe( mqttConnection,
                                pSubscriptionList,
                                subscriptionCount,
                                IOT_MQTT_FLAG_WAITABLE,
                                NULL,
                                &subscribeRef );

    /* Wait for the SUBSCRIBE operation to complete. */
    if( status == IOT_MQTT_STATUS_PENDING )
    {
        status = IotMqtt_Wait( subscribeRef, timeoutMs );
    }

    /* Ensure that a status was set. */
    IotMqtt_Assert( status != IOT_MQTT_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Unsubscribe( IotMqttConnection_t mqttConnection,
                                    const IotMqttSubscription_t * const pSubscriptionList,
                                    size_t subscriptionCount,
                                    uint32_t flags,
                                    const IotMqttCallbackInfo_t * const pCallbackInfo,
                                    IotMqttReference_t * const pUnsubscribeRef )
{
    return _subscriptionCommon( IOT_MQTT_UNSUBSCRIBE,
                                mqttConnection,
                                pSubscriptionList,
                                subscriptionCount,
                                flags,
                                pCallbackInfo,
                                pUnsubscribeRef );
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_TimedUnsubscribe( IotMqttConnection_t mqttConnection,
                                         const IotMqttSubscription_t * const pSubscriptionList,
                                         size_t subscriptionCount,
                                         uint32_t flags,
                                         uint64_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttReference_t unsubscribeRef = IOT_MQTT_REFERENCE_INITIALIZER;

    /* Flags are not used, but the parameter is present for future compatibility. */
    ( void ) flags;

    /* Call the asynchronous UNSUBSCRIBE function. */
    status = IotMqtt_Unsubscribe( mqttConnection,
                                  pSubscriptionList,
                                  subscriptionCount,
                                  IOT_MQTT_FLAG_WAITABLE,
                                  NULL,
                                  &unsubscribeRef );

    /* Wait for the UNSUBSCRIBE operation to complete. */
    if( status == IOT_MQTT_STATUS_PENDING )
    {
        status = IotMqtt_Wait( unsubscribeRef, timeoutMs );
    }

    /* Ensure that a status was set. */
    IotMqtt_Assert( status != IOT_MQTT_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Publish( IotMqttConnection_t mqttConnection,
                                const IotMqttPublishInfo_t * const pPublishInfo,
                                uint32_t flags,
                                const IotMqttCallbackInfo_t * const pCallbackInfo,
                                IotMqttReference_t * const pPublishRef )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pPublishOperation = NULL;
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) mqttConnection;

    /* Default PUBLISH serializer function. */
    IotMqttError_t ( * serializePublish )( const IotMqttPublishInfo_t * const,
                                           uint8_t ** const,
                                           size_t * const,
                                           uint16_t * const ) = _IotMqtt_SerializePublish;

    /* Choose a PUBLISH serializer function. */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->network.serialize.publish != NULL )
        {
            serializePublish = pMqttConnection->network.serialize.publish;
        }
    #endif

    /* Check that the PUBLISH information is valid. */
    if( _IotMqtt_ValidatePublish( pMqttConnection->awsIotMqttMode,
                                  pPublishInfo ) == false )
    {
        return IOT_MQTT_BAD_PARAMETER;
    }

    /* Check that no notification is requested for a QoS 0 publish. */
    if( pPublishInfo->QoS == 0 )
    {
        if( ( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE ) ||
            ( pCallbackInfo != NULL ) )
        {
            IotLogError( "QoS 0 PUBLISH should not have notification parameters set." );

            return IOT_MQTT_BAD_PARAMETER;
        }

        if( pPublishRef != NULL )
        {
            IotLogWarn( "Ignoring pPublishRef parameter for QoS 0 publish." );
        }
    }

    /* Check that a reference pointer is provided for a waitable operation. */
    if( ( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE ) &&
        ( pPublishRef == NULL ) )
    {
        IotLogError( "Reference must be provided for a waitable PUBLISH." );

        return IOT_MQTT_BAD_PARAMETER;
    }

    /* Create a PUBLISH operation. */
    status = _IotMqtt_CreateOperation( &pPublishOperation,
                                       flags,
                                       pCallbackInfo );

    if( status != IOT_MQTT_SUCCESS )
    {
        return status;
    }

    /* Check the PUBLISH operation data and set the remaining members. */
    IotMqtt_Assert( pPublishOperation->status == IOT_MQTT_STATUS_PENDING );
    pPublishOperation->operation = IOT_MQTT_PUBLISH_TO_SERVER;
    pPublishOperation->pMqttConnection = pMqttConnection;

    /* Generate a PUBLISH packet from pPublishInfo. */
    status = serializePublish( pPublishInfo,
                               &( pPublishOperation->pMqttPacket ),
                               &( pPublishOperation->packetSize ),
                               &( pPublishOperation->packetIdentifier ) );

    if( status != IOT_MQTT_SUCCESS )
    {
        _IotMqtt_DestroyOperation( pPublishOperation );

        return status;
    }

    /* Check the serialized MQTT packet. */
    IotMqtt_Assert( pPublishOperation->pMqttPacket != NULL );
    IotMqtt_Assert( pPublishOperation->packetSize > 0 );

    if( pPublishInfo->QoS == 0 )
    {
        IotMqtt_Assert( pPublishOperation->packetIdentifier == 0 );
    }
    else
    {
        IotMqtt_Assert( pPublishOperation->packetIdentifier != 0 );
    }

    /* Initialize PUBLISH retry if retryLimit is set. */
    if( pPublishInfo->retryLimit > 0 )
    {
        /* A QoS 0 PUBLISH may not be retried. */
        if( pPublishInfo->QoS > 0 )
        {
            pPublishOperation->retry.limit = pPublishInfo->retryLimit;
            pPublishOperation->retry.nextPeriod = pPublishInfo->retryMs;
        }
    }

    /* Set the reference, if provided. This should be set before the publish
     * is pushed to the send queue to avoid a race condition. */
    if( ( pPublishInfo->QoS > 0 ) && ( pPublishRef != NULL ) )
    {
        *pPublishRef = pPublishOperation;
    }

    /* Add the PUBLISH operation to the send queue for network transmission. */
    if( _IotMqtt_ScheduleOperation( pPublishOperation,
                                    _IotMqtt_ProcessSend ) != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to enqueue PUBLISH for sending." );

        _IotMqtt_DestroyOperation( pPublishOperation );

        /* Clear the previously set (and now invalid) reference. */
        if( ( pPublishInfo->QoS > 0 ) && ( pPublishRef != NULL ) )
        {
            *pPublishRef = IOT_MQTT_REFERENCE_INITIALIZER;
        }

        return IOT_MQTT_NO_MEMORY;
    }

    /* A QoS 0 PUBLISH is considered successful as soon as it is added to the
     * send queue. */
    if( pPublishInfo->QoS == 0 )
    {
        return IOT_MQTT_SUCCESS;
    }

    IotLogInfo( "MQTT PUBLISH operation queued." );

    /* QoS 1 and QoS 2 PUBLISH messages are awaiting responses. */
    return IOT_MQTT_STATUS_PENDING;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_TimedPublish( IotMqttConnection_t mqttConnection,
                                     const IotMqttPublishInfo_t * const pPublishInfo,
                                     uint32_t flags,
                                     uint64_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttReference_t publishRef = IOT_MQTT_REFERENCE_INITIALIZER,
                       * pPublishRef = NULL;

    /* Clear the flags. */
    flags = 0;

    /* Set the waitable flag and reference for QoS 1 PUBLISH. */
    if( pPublishInfo->QoS > 0 )
    {
        flags = IOT_MQTT_FLAG_WAITABLE;
        pPublishRef = &publishRef;
    }

    /* Call the asynchronous PUBLISH function. */
    status = IotMqtt_Publish( mqttConnection,
                              pPublishInfo,
                              flags,
                              NULL,
                              pPublishRef );

    /* Wait for a queued QoS 1 PUBLISH to complete. */
    if( ( pPublishInfo->QoS > 0 ) && ( status == IOT_MQTT_STATUS_PENDING ) )
    {
        status = IotMqtt_Wait( publishRef, timeoutMs );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Wait( IotMqttReference_t reference,
                             uint64_t timeoutMs )
{
    return IOT_MQTT_STATUS_PENDING;
}

/*-----------------------------------------------------------*/

const char * IotMqtt_strerror( IotMqttError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case IOT_MQTT_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case IOT_MQTT_STATUS_PENDING:
            pMessage = "PENDING";
            break;

        case IOT_MQTT_INIT_FAILED:
            pMessage = "INITIALIZATION FAILED";
            break;

        case IOT_MQTT_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case IOT_MQTT_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case IOT_MQTT_SEND_ERROR:
            pMessage = "NETWORK SEND ERROR";
            break;

        case IOT_MQTT_SCHEDULING_ERROR:
            pMessage = "SCHEDULING ERROR";
            break;

        case IOT_MQTT_BAD_RESPONSE:
            pMessage = "BAD RESPONSE RECEIVED";
            break;

        case IOT_MQTT_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case IOT_MQTT_SERVER_REFUSED:
            pMessage = "SERVER REFUSED";
            break;

        case IOT_MQTT_RETRY_NO_RESPONSE:
            pMessage = "NO RESPONSE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

const char * IotMqtt_OperationType( IotMqttOperationType_t operation )
{
    const char * pMessage = NULL;

    switch( operation )
    {
        case IOT_MQTT_CONNECT:
            pMessage = "CONNECT";
            break;

        case IOT_MQTT_PUBLISH_TO_SERVER:
            pMessage = "PUBLISH";
            break;

        case IOT_MQTT_PUBACK:
            pMessage = "PUBACK";
            break;

        case IOT_MQTT_SUBSCRIBE:
            pMessage = "SUBSCRIBE";
            break;

        case IOT_MQTT_UNSUBSCRIBE:
            pMessage = "UNSUBSCRIBE";
            break;

        case IOT_MQTT_PINGREQ:
            pMessage = "PINGREQ";
            break;

        case IOT_MQTT_DISCONNECT:
            pMessage = "DISCONNECT";
            break;

        default:
            pMessage = "INVALID OPERATION";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

/* If the MQTT library is being tested, include a file that allows access to
 * internal functions and variables. */
#if IOT_MQTT_TEST == 1
    #include "iot_test_access_mqtt_api.c"
#endif
