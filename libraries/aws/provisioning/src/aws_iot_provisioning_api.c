/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_provisioning_api.c
 * @brief Implements most user-facing functions of the Provisioning library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Error handling include. */
#include "iot_error.h"

/* Provisioning internal include. */
#include "private/aws_iot_provisioning_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"
#include "iot_atomic.h"

/* MQTT API include */
#include "iot_mqtt.h"

/* Helper AWS */
#include "aws_iot.h"

/* Logging module */
#include "iot_logging_setup.h"

/* Validate Provisioning configuration settings. */
#if AWS_IOT_PROVISIONING_ENABLE_ASSERTS != 0 && AWS_IOT_PROVISIONING_ENABLE_ASSERTS != 1
    #error "AWS_IOT_PROVISIONING_ENABLE_ASSERTS must be 0 or 1."
#endif
#if AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS <= 0
    #error "AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS cannot be 0 or negative."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Pointer to the encoder utility that will be used for serialization
 * of payload data in the library.
 */
const IotSerializerEncodeInterface_t * _pAwsIotProvisioningEncoder = NULL;

/**
 * @brief Pointer to the decoder utility that will be used for de-serialization
 * of payload data in the library.
 */
const IotSerializerDecodeInterface_t * _pAwsIotProvisioningDecoder = NULL;

/**
 * @brief The active Provisioning operation object.
 */
static _provisioningOperation_t _activeOperation;

/**
 * @brief Timeout for MQTT operations that will be used for communicating with the fleet provisioning APIs of the AWS
 * IoT Core server.
 */
uint32_t _AwsIotProvisioningMqttTimeoutMs = AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS;

/**
 * @brief Tracks whether @ref provisioning_function_init has been called.
 *
 * API functions will fail if @ref provisioning_function_init was not called.
 */
static bool _initCalled = false;

/*------------------------------------------------------------------*/

/**
 * @brief Check if the library is initialized.
 *
 * @return `true` if AwsIotProvisioning_Init was called; `false` otherwise.
 */
static bool _checkInit( void );

/**
 * @brief A utility common for processing server responses of all Provisioning operation APIs.
 * If there is an ongoing operation, the utility processes the incoming PUBLISH message and invokes the provided parser
 * if the server response is received on the "accepted" topic.
 *
 * @param[in] pPublishData The incoming PUBLISH message information from the server.
 * @param[in] responseParser The functor to invoke for parsing a successful server response payload.
 */
static void _commonServerResponseHandler( IotMqttCallbackParam_t * const pPublishData,
                                          _provisioningServerResponseParser responseParser );


/**
 * @brief The MQTT subscription callback for the response from Provisioning CreateKeysAndCertificate service API.
 */
static void _keysAndCertificateResponseReceivedCallback( void * param1,
                                                         IotMqttCallbackParam_t * const
                                                         pPublish );

/**
 * @brief The MQTT subscription callback for the response from Provisioning's RegisterThing service API.
 */
static void _registerThingResponseReceivedCallback( void * param1,
                                                    IotMqttCallbackParam_t * const pPublish );

/**
 * @brief Sets the active operation object, #_activeOperation, to represent an active operation in progress.
 * @param[in] pUserCallback The user-provided callback information that will be copied
 * to the active operation object.
 */
static void _setActiveOperation( const _provisioningCallbackInfo_t * pUserCallback );

/**
 * @brief Resets the active operation object.
 * @note This function should be called ONLY if the operation object mutex is not destroyed.
 */
static void _resetActiveOperationData();

/**
 * @brief Waits for server response within the provided timeout period, and returns the result of the wait operation.
 *
 * @param timeoutMs The time period (in milliseconds) to wait for server response.
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if a server response is received within the @p timeoutMs period; otherwise returns
 * #AWS_IOT_PROVISIONING_TIMEOUT
 */
static AwsIotProvisioningError_t _timedWaitForServerResponse( uint32_t timeoutMs );

/**
 * @brief Checks whether the data that is provided to send along with the provisioning device request is valid.
 * @param pRequestData The data for the RegisterThing service API request whose validity will be checked.
 * @return Returns `true` if data is valid; `false` otherwise.
 */
static bool _isDataForRegisterThingRequestValid( const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData );

/*------------------------------------------------------------------*/

static bool _checkInit( void )
{
    bool status = true;

    if( _initCalled == false )
    {
        IotLogError( "AwsIotProvisioning_Init was not called." );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void _commonServerResponseHandler( IotMqttCallbackParam_t * const pPublishData,
                                          _provisioningServerResponseParser responseParser )
{
    AwsIotStatus_t responseStatus = AWS_IOT_UNKNOWN;

    /* Determine whether the mutex is still valid (i.e. not destroyed) based on the reference count. If the mutex is
     * valid, indicate that we will be accessing the mutex by incrementing the reference count.
     * This tackles the RACE CONDITION with the possible cleanup of the mutex in the thread executing an Provisioning
     * Library API.*/
    if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) > 0 )
    {
        /* We will use a non-blocking mutex acquiring call to account for scenario
         * when server response is received after the mutex is destroyed
         * and thus, no longer valid. */
        IotMutex_Lock( &_activeOperation.lock );

        /* Is a user thread waiting for the result? */
        if( ( _activeOperation.info.userCallback.createKeysAndCertificateCallback.function == NULL ) ||
            ( _activeOperation.info.userCallback.registerThingCallback.function == NULL ) )
        {
            IotLogDebug( "Received unexpected server response on topic %s.",
                         pPublishData->u.message.pTopicFilter,
                         pPublishData->u.message.topicFilterLength );
        }
        else
        {
            /* Determine whether the response from the server is "accepted" or "rejected". */
            responseStatus = AwsIot_ParseStatus( pPublishData->u.message.pTopicFilter,
                                                 pPublishData->u.message.topicFilterLength );

            if( responseStatus == AWS_IOT_UNKNOWN )
            {
                IotLogWarn( "Unknown parsing status on topic %s. Ignoring message.",
                            pPublishData->u.message.pTopicFilter,
                            pPublishData->u.message.topicFilterLength );
                _activeOperation.info.status = AWS_IOT_PROVISIONING_INTERNAL_FAILURE;
            }
            else
            {
                /* Parse the server response and execute the user callback. */
                _activeOperation.info.status = responseParser(
                    responseStatus,
                    pPublishData->u.message.info.pPayload,
                    pPublishData->u.message.info.payloadLength,
                    &_activeOperation.info.userCallback );
            }

            /* Notify the waiting thread about arrival of response from server */
            /* Increment the number of PUBLISH messages received. */
            IotSemaphore_Post( &_activeOperation.responseReceivedSem );

            /* Invalidate the user-callback information to prevent re-processing the response
             * if we receive the same response multiple times (which is possible for a QoS 1 publish
             * from the server). This is done to post on the semaphore ONLY ONCE on receiving the
             * response from the server.*/
            memset( &_activeOperation.info.userCallback, 0, sizeof( _activeOperation.info.userCallback ) );
        }

        IotMutex_Unlock( &_activeOperation.lock );
    }

    /* Decrement the mutex reference count, as we don't need the mutex anymore.
     * If there is no other thread/context is alive that needs the mutex, then we will destroy it. */
    if( Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount ) == 1 )
    {
        IotMutex_Destroy( &_activeOperation.lock );
    }
}

/*-----------------------------------------------------------*/

static void _keysAndCertificateResponseReceivedCallback( void * param1,
                                                         IotMqttCallbackParam_t * const pPublish )
{
    /* Silence warnings about unused variables.*/
    ( void ) param1;

    _commonServerResponseHandler( pPublish, _AwsIotProvisioning_ParseKeysAndCertificateResponse );
}

/*-----------------------------------------------------------*/

static void _registerThingResponseReceivedCallback( void * param1,
                                                    IotMqttCallbackParam_t * const pPublish )
{
    /* Silence warnings about unused variables.*/
    ( void ) param1;

    _commonServerResponseHandler( pPublish, _AwsIotProvisioning_ParseRegisterThingResponse );
}

/*-----------------------------------------------------------*/

static void _resetActiveOperationData()
{
    /* Determine whether the mutex is still valid (i.e. not destroyed) based on the reference count. If the mutex is
     * valid, indicate that we will be accessing the mutex by incrementing the reference count.*/
    if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) > 0 )
    {
        IotMutex_Lock( &( _activeOperation.lock ) );
        {
            memset( &_activeOperation.info.userCallback, 0, sizeof( _activeOperation.info.userCallback ) );
        }
        IotMutex_Unlock( &( _activeOperation.lock ) );

        IotSemaphore_TryWait( &_activeOperation.responseReceivedSem );
    }

    /* Reverse the previous increment operation as we don't need the mutex anymore. */
    ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
}

/*-----------------------------------------------------------*/

static void _setActiveOperation( const _provisioningCallbackInfo_t * pUserCallback )
{
    /* Increment the reference count as we will be acquiring the mutex. */
    if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) != 0 )
    {
        /* Update shared active operation object to indicate that an operation is in
         * progress. */
        IotMutex_Lock( &( _activeOperation.lock ) );
        {
            /* If a successful response is not received, it should be treated as
             * MQTT error. */
            _activeOperation.info.status = AWS_IOT_PROVISIONING_MQTT_ERROR;

            /* Store the user supplied callback. */
            _activeOperation.info.userCallback = *pUserCallback;
        }
        IotMutex_Unlock( &( _activeOperation.lock ) );
    }

    /* Decrement the reference count as we have released the mutex. */
    ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
}

/*-----------------------------------------------------------*/

static bool _isDataForRegisterThingRequestValid( const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData )
{
    IOT_FUNCTION_ENTRY( bool, true );

    if( pRequestData == NULL )
    {
        IotLogError( "Invalid request data passed for provisioning device." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    if( ( pRequestData->pDeviceCertificateId == NULL ) ||
        ( pRequestData->deviceCertificateIdLength == 0 ) )
    {
        IotLogError( "Invalid certificate ID data passed for device provisioning request." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    if( ( pRequestData->pCertificateOwnershipToken == NULL ) ||
        ( pRequestData->ownershipTokenLength == 0 ) )
    {
        IotLogError( "Invalid certificate ownership token data passed for device provisioning request." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Check that the provided template name is valid. */
    if( ( pRequestData->pTemplateName == NULL ) ||
        ( pRequestData->templateNameLength == 0 ) ||
        ( pRequestData->templateNameLength > PROVISIONING_MAX_TEMPLATE_NAME_LENGTH ) )
    {
        IotLogError( "Invalid template name information passed for device provisioning request." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}
/*-----------------------------------------------------------*/

static AwsIotProvisioningError_t _timedWaitForServerResponse( uint32_t timeoutMs )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_TIMEOUT;

    /* Wait for response from the server. */
    if( ( IotSemaphore_TimedWait( &_activeOperation.responseReceivedSem, timeoutMs ) == true )
        &&
        ( _activeOperation.info.status != AWS_IOT_PROVISIONING_MQTT_ERROR ) )
    {
        /* Use the status value calculated from processing the server response in the MQTT callback. */
        status = _activeOperation.info.status;
    }
    else
    {
        /* Do nothing as the default return status value is set to timeout. */
    }

    return status;
}

/*-----------------------------------------------------------*/

AwsIotProvisioningError_t AwsIotProvisioning_Init( uint32_t mqttTimeoutMs )
{
    bool mutexCreated = false;

    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );

    if( _initCalled == false )
    {
        _initCalled = true;

        /* Get the pointers to the encoder function tables. */
        #if AWS_IOT_PROVISIONING_FORMAT == AWS_IOT_PROVISIONING_FORMAT_CBOR
            _pAwsIotProvisioningDecoder = IotSerializer_GetCborDecoder();
            _pAwsIotProvisioningEncoder = IotSerializer_GetCborEncoder();
        #endif

        /* Create the mutex guarding the operation object. */
        if( IotMutex_Create( &( _activeOperation.lock ), false ) == false )
        {
            IotLogError( "Failed to initialize Provisioning library due to mutex creation failure." );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INIT_FAILED );
        }
        else
        {
            mutexCreated = true;

            /* Initialize the reference count to one as the mutex to represent that there is a single thread/context
             * alive that needs the mutex.
             * If the reference count is already greather than 0, it represents that there is already a thread accessing
             * the mutex, which is NOT expected at initialization. */
            if( Atomic_CompareAndSwap_u32( &_activeOperation.mutexReferenceCount, 1u, 0u ) == 0 )
            {
                IotLogError(
                    "Failed to initialize Provisioning library as mutex reference counter is in an invalid state." );
                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INIT_FAILED );
            }
        }

        /* Save the MQTT timeout option. */
        if( mqttTimeoutMs != 0 )
        {
            _AwsIotProvisioningMqttTimeoutMs = mqttTimeoutMs;
        }

        _resetActiveOperationData();

        /* Create a binary semaphore needed for signaling arrival of server responses. */
        if( IotSemaphore_Create( &( _activeOperation.responseReceivedSem ),
                                 0 /* initialValue */,
                                 1 /* maxValue */ ) == false )
        {
            IotLogError(
                "Failed to initialize Provisioning library due to semaphore creation failure." );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INIT_FAILED );
        }

        IotLogInfo( "Provisioning library successfully initialized." );

        IOT_FUNCTION_CLEANUP_BEGIN();

        if( status != AWS_IOT_PROVISIONING_SUCCESS )
        {
            if( mutexCreated )
            {
                IotMutex_Destroy( &_activeOperation.lock );
            }

            ( void ) Atomic_AND_u32( &_activeOperation.mutexReferenceCount, 0u );
        }
    }
    else
    {
        IotLogWarn( "AwsIotProvisioning_Init called with library already initialized." );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/
AwsIotProvisioningError_t AwsIotProvisioning_CreateKeysAndCertificate( IotMqttConnection_t
                                                                       provisioningConnection,
                                                                       uint32_t flags,
                                                                       uint32_t timeoutMs,
                                                                       const AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t * keysAndCertificateResponseCallback )
{
    uint32_t startingMutexRefCount = 0;
    bool mutexRefCountIncremented = false;
    char responseTopicsBuffer[ PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_MAX_TOPIC_LENGTH ] =
    { 0 };
    IotMqttError_t mqttOpResult = IOT_MQTT_SUCCESS;
    /* Configuration for subscribing and unsubscribing to/from response topics. */
    AwsIotSubscriptionInfo_t responseSubscription =
    {
        .mqttConnection        = provisioningConnection,
        .callbackFunction      = _keysAndCertificateResponseReceivedCallback,
        .timeout               = _AwsIotProvisioningMqttTimeoutMs,
        .pTopicFilterBase      = responseTopicsBuffer,
        .topicFilterBaseLength = PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER_LENGTH
    };
    bool subscribedToResponseTopics = false;
    size_t payloadSize = 0;
    uint8_t * pPayloadBuffer = NULL;
    bool payloadBufferAllocated = false;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    /* Suppress unused variable warning. */
    ( void ) flags;
    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );

    /* Check that library has been initialized. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_NOT_INITIALIZED );
    }

    if( provisioningConnection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_PARAMETER );
    }

    /* Check that a callback function object along with a valid callback functor is provided. */
    if( ( keysAndCertificateResponseCallback == NULL ) ||
        ( keysAndCertificateResponseCallback->function == NULL ) )
    {
        IotLogError(
            "Invalid callback provided. Both the callback object and functor within should be provided to the %s operation",
            CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_PARAMETER );
    }

    /* Increment the reference counter to indicate that mutex is required. */
    startingMutexRefCount = Atomic_Increment_u32( &_activeOperation.mutexReferenceCount );
    mutexRefCountIncremented = true;

    if( startingMutexRefCount == 0u )
    {
        IotLogError( "Mutex is unavailable for API operation." );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    /* Copy the response topics in a local buffer for appropriate suffixes to be added. */
    ( void ) memcpy( responseTopicsBuffer, PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER,
                     PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER_LENGTH );

    /* Subscribe to the MQTT response topics. */
    mqttOpResult = AwsIot_ModifySubscriptions( IotMqtt_SubscribeSync, &responseSubscription );

    if( mqttOpResult != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Unable to subscribe to response topics for %s operation",
                     CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_MQTT_ERROR );
    }
    else
    {
        subscribedToResponseTopics = true;
    }

    /* Update the operation object to represent an active "get device credentials" operation. */
    _provisioningCallbackInfo_t callbackInfo;
    callbackInfo.createKeysAndCertificateCallback = *keysAndCertificateResponseCallback;
    _setActiveOperation( &callbackInfo );

    /* Provisioning already has an acknowledgement mechanism, so sending the message at
     * QoS 1 provides no benefit. */
    publishInfo.qos = IOT_MQTT_QOS_0;

    /* Generate the serialized payload for requesting provisioning of the device.*/

    status = _AwsIotProvisioning_SerializeCreateKeysAndCertificateRequestPayload( &pPayloadBuffer,
                                                                                  &payloadSize );

    if( pPayloadBuffer == NULL )
    {
        IotLogError( "Unable to allocate memory for request payload in %s API operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_NO_MEMORY );
    }
    else
    {
        payloadBufferAllocated = true;
    }

    publishInfo.pPayload = pPayloadBuffer;
    publishInfo.payloadLength = payloadSize;

    /* Set the operation topic name. */
    publishInfo.pTopicName = PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC;
    publishInfo.topicNameLength = PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC_LENGTH;

    IotLogDebug( "Provisioning %s message will be published to topic %.*s",
                 CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG,
                 publishInfo.topicNameLength,
                 publishInfo.pTopicName );

    /* Publish to the Provisioning topic name. */
    mqttOpResult = IotMqtt_PublishSync( provisioningConnection,
                                        &publishInfo,
                                        0,
                                        _AwsIotProvisioningMqttTimeoutMs );

    if( mqttOpResult != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Unable to subscribe to response topics for %s operation",
                     CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_MQTT_ERROR );
    }

    /* Wait for response from server using the given timeout period. */
    status = _timedWaitForServerResponse( timeoutMs );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Unsubscribe from the MQTT response topics only if subscription to those topics was successful. */
    if( subscribedToResponseTopics )
    {
        AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                    &responseSubscription );
    }

    if( payloadBufferAllocated )
    {
        AwsIotProvisioning_FreePayload( pPayloadBuffer );
    }

    /* Reset the active operation */
    _resetActiveOperationData();

    /* Indicate that the mutex is no longer required by the API as its execution lifetime is ending. */
    if( mutexRefCountIncremented )
    {
        ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

AwsIotProvisioningError_t AwsIotProvisioning_CreateCertificateFromCsr( IotMqttConnection_t connection,
                                                                       const char * pCertificateSigningRequest,
                                                                       size_t csrLength,
                                                                       uint32_t timeoutMs,
                                                                       const AwsIotProvisioningCreateCertificateFromCsrCallbackInfo_t * pResponseCallback )
{
    uint32_t startingMutexRefCount = 0;
    bool mutexRefCountIncremented = false;
    char responseTopicsBuffer[ PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_MAX_TOPIC_LENGTH ] =
    { 0 };
    IotMqttError_t mqttOpResult = IOT_MQTT_SUCCESS;
    /* Configuration for subscribing and unsubscribing to/from response topics. */
    AwsIotSubscriptionInfo_t responseSubscription =
    {
        .mqttConnection        = connection,
        .callbackFunction      = _keysAndCertificateResponseReceivedCallback,
        .timeout               = _AwsIotProvisioningMqttTimeoutMs,
        .pTopicFilterBase      = responseTopicsBuffer,
        .topicFilterBaseLength = PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER_LENGTH
    };
    bool subscribedToResponseTopics = false;
    size_t payloadSize = 0;
    uint8_t * pPayloadBuffer = NULL;
    bool payloadBufferAllocated = false;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    /* Verify that library has been initialized. */
    AwsIotProvisioning_Assert( _checkInit() == true );

    if( connection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized." );

        status = AWS_IOT_PROVISIONING_BAD_PARAMETER;
    }
    else if( ( pCertificateSigningRequest == NULL ) || ( csrLength == 0 ) )
    {
        IotLogError( "Invalid Certificate-Signing Request data passed." );

        status = AWS_IOT_PROVISIONING_BAD_PARAMETER;
    }
    /* Check that a callback function object along with a valid callback functor is provided. */
    else if( ( pResponseCallback == NULL ) ||
             ( pResponseCallback->function == NULL ) )
    {
        IotLogError(
            "Invalid callback provided. Both the callback object and functor within should be provided to the %s operation",
            CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );

        status = AWS_IOT_PROVISIONING_BAD_PARAMETER;
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Copy the response topics in a local buffer for appropriate suffixes to be added. */
        ( void ) memcpy( responseTopicsBuffer, PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER,
                         PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER_LENGTH );

        /* Subscribe to the MQTT response topics. */
        mqttOpResult = AwsIot_ModifySubscriptions( IotMqtt_SubscribeSync, &responseSubscription );

        if( mqttOpResult != IOT_MQTT_SUCCESS )
        {
            IotLogError( "Unable to subscribe to response topics for %s operation",
                         CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );
            status = AWS_IOT_PROVISIONING_MQTT_ERROR;
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Update the operation object to represent an active "Certificate-Signing Request" operation. */
        _provisioningCallbackInfo_t callbackInfo;
        callbackInfo.createKeysAndCertificateCallback = *pResponseCallback;
        _setActiveOperation( &callbackInfo );

        /* Provisioning already has an acknowledgement mechanism, so sending the message at
         * QoS 1 provides no benefit. */
        publishInfo.qos = IOT_MQTT_QOS_0;

        /* TODO - Decide on memory allocation scheme. Should the memory be allocated here with 2-step serialization process? */
        /* Dry run serialization */
        _AwsIotProvisioning_SerializeCreateCertificateFromCsrRequestPayload( pCertificateSigningRequest,
                                                                             csrLength,
                                                                             NULL,
                                                                             &payloadSize );
        AwsIotProvisioning_Assert( payloadSize != 0 );

        /* Allocate memory for payload buffer based on calculated serialization size. */
        pPayloadBuffer = AwsIotProvisioning_MallocPayload( pPayloadBuffer );

        if( pPayloadBuffer == NULL )
        {
            IotLogError( "Unable to allocate memory for request payload in %s API operation",
                         REGISTER_THING_OPERATION_LOG );
            status = AWS_IOT_PROVISIONING_NO_MEMORY;
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Actual serialization in payload buffer. */
        _AwsIotProvisioning_SerializeCreateCertificateFromCsrRequestPayload( pCertificateSigningRequest,
                                                                             csrLength,
                                                                             pPayloadBuffer,
                                                                             &payloadSize );

        publishInfo.pPayload = pPayloadBuffer;
        publishInfo.payloadLength = payloadSize;

        /* Set the operation topic name. */
        publishInfo.pTopicName = PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC;
        publishInfo.topicNameLength = PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC_LENGTH;

        IotLogDebug( "About to publish %.*s topic for the %s operation",
                     publishInfo.topicNameLength,
                     publishInfo.pTopicName,
                     CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );

        /* Publish to the Provisioning topic name. */
        mqttOpResult = IotMqtt_PublishSync( connection,
                                            &publishInfo,
                                            0,
                                            _AwsIotProvisioningMqttTimeoutMs );

        if( mqttOpResult != IOT_MQTT_SUCCESS )
        {
            IotLogError( "Unable to publish to request topic for %s operation",
                         CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );
            status = AWS_IOT_PROVISIONING_MQTT_ERROR;
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Wait for response from server using the given timeout period. */
        status = _timedWaitForServerResponse( timeoutMs );

        /* Unsubscribe from the MQTT response topics only if subscription to those topics was successful. */
        AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                    &responseSubscription );

        AwsIotProvisioning_FreePayload( pPayloadBuffer );
    }

    /* Reset the active operation */
    _resetActiveOperationData();

    return status;
}

/*-----------------------------------------------------------*/

AwsIotProvisioningError_t AwsIotProvisioning_RegisterThing( IotMqttConnection_t provisioningConnection,
                                                            const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData,
                                                            uint32_t timeoutMs,
                                                            const AwsIotProvisioningRegisterThingCallbackInfo_t * pResponseCallback )
{
    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );
    IotMqttError_t mqttOpResult = IOT_MQTT_SUCCESS;
    uint32_t startingMutexRefCount = 0;
    bool mutexRefCountIncremented = false;

    /* Use the same buffer for storing the request and response MQTT topic strings (for space efficiency) as both kinds
     * of topics share the same filter. */
    char requestResponseTopicsBuffer[ PROVISIONING_REGISTER_THING_RESPONSE_MAX_TOPIC_LENGTH ] = { 0 };
    size_t generatedTopicFilterSize = 0;
    AwsIotProvisioning_Assert( PROVISIONING_REGISTER_THING_RESPONSE_MAX_TOPIC_LENGTH >
                               PROVISIONING_REGISTER_THING_REQUEST_TOPIC_LENGTH );

    bool subscribedToResponseTopics = false;
    /* Configuration for subscribing and unsubscribing to/from response topics. */
    AwsIotSubscriptionInfo_t responseSubscription =
    {
        .mqttConnection        = provisioningConnection,
        .callbackFunction      = _registerThingResponseReceivedCallback,
        .timeout               = _AwsIotProvisioningMqttTimeoutMs,
        .pTopicFilterBase      = requestResponseTopicsBuffer,
        .topicFilterBaseLength = PROVISIONING_REGISTER_THING_RESPONSE_TOPIC_FILTER_LENGTH
    };

    size_t payloadSize = 0;
    uint8_t * pPayloadBuffer = NULL;
    bool payloadBufferAllocated = false;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    /* Check that library has been initialized. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_NOT_INITIALIZED );
    }

    if( provisioningConnection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_PARAMETER );
    }

    if( _isDataForRegisterThingRequestValid( pRequestData ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_PARAMETER );
    }

    /* Check that a callback function object along with a valid callback functor is provided. */
    if( ( pResponseCallback == NULL ) || ( pResponseCallback->function == NULL ) )
    {
        IotLogError(
            "Invalid callback provided. A valid callback object and functor should be provided to the %s operation",
            REGISTER_THING_OPERATION_LOG );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_PARAMETER );
    }

    /* Increment the reference counter to indicate that mutex is required. */
    startingMutexRefCount = Atomic_Increment_u32( &_activeOperation.mutexReferenceCount );
    mutexRefCountIncremented = true;

    if( startingMutexRefCount == 0u )
    {
        IotLogError( "Mutex is unavailable for API operation." );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    /* Generate the response topic filter using the template ID. */
    generatedTopicFilterSize = _AwsIotProvisioning_GenerateRegisterThingTopicFilter(
        pRequestData->pTemplateName,
        pRequestData->templateNameLength,
        requestResponseTopicsBuffer );

    if( generatedTopicFilterSize == 0 )
    {
        IotLogError( "Unable to generate MQTT topic filter for topics related to %s operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    responseSubscription.topicFilterBaseLength = generatedTopicFilterSize;

    /* Subscribe to the MQTT response topics. */
    mqttOpResult = AwsIot_ModifySubscriptions( IotMqtt_TimedSubscribe, &responseSubscription );

    if( mqttOpResult != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Unable to subscribe to response topics for %s operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_MQTT_ERROR );
    }
    else
    {
        subscribedToResponseTopics = true;
    }

    /* Update the operation object to represent an active "register thing" operation. */
    _provisioningCallbackInfo_t callbackInfo;
    callbackInfo.registerThingCallback = *pResponseCallback;
    _setActiveOperation( &callbackInfo );

    /* Provisioning already has an acknowledgement mechanism, so sending the message at
     * QoS 1 provides no benefit. */
    publishInfo.qos = IOT_MQTT_QOS_0;

    /* Generate the serialized payload for requesting provisioning of the device.*/

    status = _AwsIotProvisioning_SerializeRegisterThingRequestPayload( pRequestData,
                                                                       &pPayloadBuffer,
                                                                       &payloadSize );

    if( pPayloadBuffer == NULL )
    {
        IotLogError( "Unable to allocate memory for request payload in %s API operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_NO_MEMORY );
    }
    else
    {
        payloadBufferAllocated = true;
    }

    if( status != AWS_IOT_PROVISIONING_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Set the payload for the device provisioning request. */
    publishInfo.pPayload = pPayloadBuffer;
    publishInfo.payloadLength = payloadSize;

    /* Set the request topic to PUBLISH to.
     * Note: For memory and performance efficiency, we are using the same buffer as the response topics. We specify the
     * length of the buffer that is applicable to the request topic. */
    publishInfo.pTopicName = requestResponseTopicsBuffer;
    publishInfo.topicNameLength = generatedTopicFilterSize;

    IotLogDebug( "Provisioning %s message will be published to topic %.*s",
                 REGISTER_THING_OPERATION_LOG,
                 publishInfo.topicNameLength,
                 publishInfo.pTopicName );

    /* Publish to the Provisioning topic name. */
    mqttOpResult = IotMqtt_TimedPublish( provisioningConnection,
                                         &publishInfo,
                                         0,
                                         _AwsIotProvisioningMqttTimeoutMs );

    if( mqttOpResult != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Unable to subscribe to response topics for %s operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_MQTT_ERROR );
    }

    /* Wait for response from server using the given timeout period. */
    status = _timedWaitForServerResponse( timeoutMs );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Unsubscribe from the MQTT response topics only if subscription to those topics was successful. */
    if( subscribedToResponseTopics )
    {
        AwsIot_ModifySubscriptions( IotMqtt_TimedUnsubscribe,
                                    &responseSubscription );
    }

    if( payloadBufferAllocated )
    {
        AwsIotProvisioning_FreePayload( pPayloadBuffer );
    }

    /* Reset the active operation */
    _resetActiveOperationData();

    /* Indicate that the mutex is no longer required by the API as its execution lifetime is ending. */
    if( mutexRefCountIncremented )
    {
        ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
    }

    IOT_FUNCTION_CLEANUP_END();
}


/*-----------------------------------------------------------*/

void AwsIotProvisioning_Cleanup( void )
{
    if( _initCalled == true )
    {
        /* Reset the flag to indicate that library will have to be re-initialized to use it again. */
        _initCalled = false;

        _AwsIotProvisioningMqttTimeoutMs = AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS;

        /* Determine whether the mutex is still valid (i.e. not destroyed) based on the reference count. If the mutex is
         * valid, indicate that we will be accessing the mutex by incrementing the reference count.
         * This tackles the RACE CONDITION with the possible cleanup of the mutex in the thread executing an
         * Provisioning
         * Library API.*/
        if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) > 0 )
        {
            _resetActiveOperationData();
        }

        /* Reverse the previous increment operation as we don't need the mutex anymore. */
        ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );

        /* We will destroy the mutex only if there is no other thread/context alive that needs the mutex.
         * This tackles the race condition with the execution of an MQTT callback (that was registered by the operation
         * APIs) accessing the mutex.*/
        if( Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount ) == 1 )
        {
            IotMutex_Destroy( &( _activeOperation.lock ) );
        }

        IotSemaphore_Destroy( &( _activeOperation.responseReceivedSem ) );

        IotLogInfo( "Provisioning library cleanup done." );
    }
    else
    {
        IotLogWarn( "AwsIotProvisioning_Init was not called before AwsIotProvisioning_Cleanup." );
    }
}

/*-----------------------------------------------------------*/

const char * AwsIotProvisioning_strerror( AwsIotProvisioningError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case AWS_IOT_PROVISIONING_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case AWS_IOT_PROVISIONING_INIT_FAILED:
            pMessage = "INIT FAILED";
            break;

        case AWS_IOT_PROVISIONING_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case AWS_IOT_PROVISIONING_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case AWS_IOT_PROVISIONING_MQTT_ERROR:
            pMessage = "MQTT ERROR";
            break;

        case AWS_IOT_PROVISIONING_SERVER_REFUSED:
            pMessage = "SERVER REFUSED";
            break;

        case AWS_IOT_PROVISIONING_BAD_RESPONSE:
            pMessage = "BAD RESPONSE";
            break;

        case AWS_IOT_PROVISIONING_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case AWS_IOT_PROVISIONING_INTERNAL_FAILURE:
            pMessage = "FAILED: INTERNAL FAILURE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/
