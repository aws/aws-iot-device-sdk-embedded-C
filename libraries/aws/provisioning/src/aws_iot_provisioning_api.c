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
 * @brief An operation object instance for each of the 3 operations:
 * CreateKeysAndCertificate, CreateCertificateFromCsr, RegisterThing.
 */
static _provisioningOperation_t _activeOperation[ 3 ];

/**
 * @brief The index reference to the operation object
 * in #_activeOperation array for the CreateKeysAndCertificate
 * operation.
 */
static const uint8_t _createKeysAndCertOperationIndex = 0;

/**
 * @brief The index reference to the operation object
 * in #_activeOperation array for the CreateCertificateFromCsr
 * operation.
 */
static const uint8_t _createCertFromCsrOperationIndex = 1;

/**
 * @brief The index reference to the operation object
 * in #_activeOperation array for the RegisterThing
 * operation.
 */
static const uint8_t _registerThingOperationIndex = 2;

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
 * @brief Initializes the operation object in #_activeOperation array for the
 * passed index reference.
 *
 * @param[in] operationIndex The index reference to the operation object instance to initialize.
 *
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if initialization is successful;
 * otherwise #AWS_IOT_PROVISIONING_INIT_FAILED.
 */
static AwsIotProvisioningError_t _initializeOperationObject( uint8_t operationIndex );

/**
 * @brief Cleans up the operation object in #_activeOperation array for the
 * passed index reference.
 *
 * @param[in] operationIndex The index reference to the operation object instance to clean-up.
 */
static void _cleanUpOperationObject( uint8_t operationIndex );

/**
 * @brief A utility common for processing server responses of all Provisioning operation APIs.
 * If there is an ongoing operation, the utility processes the incoming PUBLISH message and invokes the provided parser
 * if the server response is received on the "accepted" topic.
 *
 * @param[in] operationIndex The index reference of the operation to the
 * #_activeOperation array.
 * @param[in] pPublishData The incoming PUBLISH message information from the server.
 * @param[in] responseParser The functor to invoke for parsing a successful server response payload.
 */
static void _commonServerResponseHandler( const uint8_t operationIndex,
                                          IotMqttCallbackParam_t * const pPublishData,
                                          _provisioningServerResponseParser responseParser );


/**
 * @brief The common MQTT subscription callback for response topics of the
 * CreateKeysAndCertificate service API.
 */
static void _keysAndCertificateResponseReceivedCallback( void * param1,
                                                         IotMqttCallbackParam_t * const
                                                         pPublish );

/**
 * @brief The common MQTT subscription callback for response topics of the
 * CreateCertificateFromCsr service API.
 */
static void _csrResponseReceivedCallback( void * param1,
                                          IotMqttCallbackParam_t * const pPublish );

/**
 * @brief The common MQTT subscription callback for the response topics
 * of the RegisterThing service API.
 */
static void _registerThingResponseReceivedCallback( void * param1,
                                                    IotMqttCallbackParam_t * const pPublish );

/**
 * @brief Sets an operation object in the #_activeOperation array to represent
 * an active operation in progress.
 * @param[in] operationIndex The index reference to the ongoing operation
 * object in the #_activeOperation array.
 * @param[in] pUserCallback The user-provided callback information that will be copied
 * to the active operation object.
 */
static void _setActiveOperation( uint8_t operationIndex,
                                 const _provisioningCallbackInfo_t * pUserCallback );

/**
 * @brief Waits for server response within the provided timeout period, and returns the result of the wait operation.
 *
 * @param[in] operationIndex The index reference to the ongoing operation
 * object in the #_activeOperation array.
 * @param[in] timeoutMs The time period (in milliseconds) to wait for server response.
 *
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if a server response is received within the @p timeoutMs period; otherwise returns
 * #AWS_IOT_PROVISIONING_TIMEOUT
 */
static AwsIotProvisioningError_t _timedWaitForServerResponse( uint8_t operationIndex,
                                                              uint32_t timeoutMs );

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

static AwsIotProvisioningError_t _initializeOperationObject( uint8_t operationIndex )
{
    AwsIotProvisioning_Assert( operationIndex < sizeof( _activeOperation ) /
                               sizeof( _provisioningOperation_t ) );

    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    memset( &_activeOperation[ operationIndex ].info,
            0,
            sizeof( _activeOperation[ operationIndex ].info ) );

    /* Create a binary semaphore needed for signaling arrival of server responses. */
    if( IotSemaphore_Create( &( _activeOperation[ operationIndex ].
                                   responseReceivedSem ),
                             0u /* initialValue */,
                             1u /* maxValue */ ) == false )
    {
        IotLogError(
            "api: Unable to initialize library: Failed to create semaphore:"
            "OperationArrayIndex={%d}", operationIndex );

        status = AWS_IOT_PROVISIONING_INIT_FAILED;
    }

    /* Increment reference counter for semaphore to represent its validity. */
    if( Atomic_Increment_u32(
            &_activeOperation[ operationIndex ].semReferenceCount ) != 0u )
    {
        IotLogError( "api: Unable to initialize library: Semaphore reference "
                     "is non-zero: OperationArrayIndex={%d}", operationIndex );

        status = AWS_IOT_PROVISIONING_INIT_FAILED;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void _cleanUpOperationObject( uint8_t operationIndex )
{
    /*
     * Check whether the operation semaphore is being accessed by another thread
     * context, before destroying the resource.
     * This tackles the RACE CONDITION of concurrent access of the semaphore
     * with the MQTT subscription callback context (on an incoming server response,
     * specifically, for MQTT QoS 1 incoming PUBLISHes).
     */
    if( Atomic_CompareAndSwap_u32( &_activeOperation[ operationIndex ].semReferenceCount,
                                   0u,
                                   1u ) == 1u )
    {
        /* Semaphore is safe to destroy as no other context is accessing it. */
        IotSemaphore_Destroy( &( _activeOperation[ operationIndex ].responseReceivedSem ) );
    }
}

/*-----------------------------------------------------------*/

static void _commonServerResponseHandler( const uint8_t operationIndex,
                                          IotMqttCallbackParam_t * const pPublishData,
                                          _provisioningServerResponseParser responseParser )
{
    /*
     * Check whether the operation's sempahore is valid. There is tackles the
     * possible RACE CONDITION between #AwsIotProvisioning_CleanUp destroying the
     * semaphore resource, and an incoming server response being processed by the
     * callback.
     */
    if( Atomic_Increment_u32( &_activeOperation[ operationIndex ].
                                 semReferenceCount ) > 0u )
    {
        AwsIotStatus_t responseStatus = AWS_IOT_UNKNOWN;
        _provisioningCallbackInfo_t * pCallbackInfo = &_activeOperation[ operationIndex ].
                                                         info.userCallback;

        /* Is a user thread waiting for the result? */
        if( ( pCallbackInfo->createKeysAndCertificateCallback.function == NULL ) ||
            ( pCallbackInfo->createCertFromCsrCallback.function == NULL ) ||
            ( pCallbackInfo->registerThingCallback.function == NULL ) )
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
                _activeOperation[ operationIndex ].info.status =
                    AWS_IOT_PROVISIONING_INTERNAL_FAILURE;
            }
            else
            {
                /* Parse the server response and execute the user callback. */
                _activeOperation[ operationIndex ].info.status = responseParser(
                    responseStatus,
                    pPublishData->u.message.info.pPayload,
                    pPublishData->u.message.info.payloadLength,
                    &_activeOperation[ operationIndex ].info.userCallback );
            }

            /* Notify the waiting thread about arrival of response from server */
            /* Increment the number of PUBLISH messages received. */
            IotSemaphore_Post( &_activeOperation[ operationIndex ].responseReceivedSem );
        }
    }
    else
    {
        IotLogWarn( "api: Unexpected invocation of subscription callback: "
                    "Clean-up on library was already called: OperationIndex={%d}",
                    operationIndex );
    }

    /* Decrement the operation's semaphore reference count, as we don't need
     * the mutex anymore.
     * If reference count is lower than the count at which we incremented at the
     * beginning of the callback, it means that the the #AwsIotProvisioning_CleanUp
     * function was called. In that case, we destroy of semaphore to clean the memory.
     */
    if( Atomic_Decrement_u32( &_activeOperation[ operationIndex ].
                                 semReferenceCount ) == 1u )
    {
        /* Semaphore is safe to destroy as no other context is accessing it. */
        IotSemaphore_Destroy( &( _activeOperation[ operationIndex ].responseReceivedSem ) );
    }
}

/*-----------------------------------------------------------*/

static void _keysAndCertificateResponseReceivedCallback( void * param1,
                                                         IotMqttCallbackParam_t * const pPublish )
{
    /* Silence warnings about unused variables.*/
    ( void ) param1;

    _commonServerResponseHandler( _createKeysAndCertOperationIndex,
                                  pPublish,
                                  _AwsIotProvisioning_ParseKeysAndCertificateResponse );
}

/*-----------------------------------------------------------*/

static void _csrResponseReceivedCallback( void * param1,
                                          IotMqttCallbackParam_t * const pPublish )
{
    /* Silence warnings about unused variables.*/
    ( void ) param1;

    _commonServerResponseHandler( _createCertFromCsrOperationIndex,
                                  pPublish,
                                  _AwsIotProvisioning_ParseCsrResponse );
}

/*-----------------------------------------------------------*/

static void _registerThingResponseReceivedCallback( void * param1,
                                                    IotMqttCallbackParam_t * const pPublish )
{
    /* Silence warnings about unused variables.*/
    ( void ) param1;

    _commonServerResponseHandler( _registerThingOperationIndex,
                                  pPublish,
                                  _AwsIotProvisioning_ParseRegisterThingResponse );
}

/*-----------------------------------------------------------*/

static void _setActiveOperation( uint8_t operationIndex,
                                 const _provisioningCallbackInfo_t * pUserCallback )
{
    /* If a successful response is not received, it should be treated as
     * MQTT error. */
    _activeOperation[ operationIndex ].info.status = 0;

    /* Store the user supplied callback. */
    _activeOperation[ operationIndex ].info.userCallback = *pUserCallback;
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

static AwsIotProvisioningError_t _timedWaitForServerResponse( uint8_t operationIndex,
                                                              uint32_t timeoutMs )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_TIMEOUT;

    /* Wait for response from the server. */
    if( ( IotSemaphore_TimedWait( &_activeOperation[ operationIndex ].responseReceivedSem,
                                  timeoutMs ) == true )
        &&
        ( _activeOperation[ operationIndex ].info.status != 0 ) )
    {
        /* Use the status value calculated from processing the server response in the MQTT callback. */
        status = _activeOperation[ operationIndex ].info.status;
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
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    if( _initCalled == false )
    {
        _initCalled = true;

        /* Get the pointers to the encoder function tables. */
        #if AWS_IOT_PROVISIONING_FORMAT == AWS_IOT_PROVISIONING_FORMAT_CBOR
            _pAwsIotProvisioningDecoder = IotSerializer_GetCborDecoder();
            _pAwsIotProvisioningEncoder = IotSerializer_GetCborEncoder();
        #endif

        /* Save the MQTT timeout option. */
        if( mqttTimeoutMs != 0 )
        {
            _AwsIotProvisioningMqttTimeoutMs = mqttTimeoutMs;
        }

        /* Initialize all operation objects instances. */
        status = _initializeOperationObject( _createKeysAndCertOperationIndex );

        if( status == AWS_IOT_PROVISIONING_SUCCESS )
        {
            status = _initializeOperationObject( _createCertFromCsrOperationIndex );
        }

        if( status == AWS_IOT_PROVISIONING_SUCCESS )
        {
            status = _initializeOperationObject( _registerThingOperationIndex );
        }

        if( status == AWS_IOT_PROVISIONING_SUCCESS )
        {
            IotLogInfo( "api: Provisioning library successfully initialized." );
        }
    }
    else
    {
        IotLogWarn( "api: Unexpected initialization of library: "
                    "Library is already initialized" );
    }

    return status;
}

/*-----------------------------------------------------------*/
AwsIotProvisioningError_t AwsIotProvisioning_CreateKeysAndCertificate( IotMqttConnection_t
                                                                       provisioningConnection,
                                                                       uint32_t flags,
                                                                       uint32_t timeoutMs,
                                                                       const AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t * keysAndCertificateResponseCallback )
{
    char responseTopicsBuffer[ PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_MAX_TOPIC_LENGTH ] =
        PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER;
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

    if( provisioningConnection == NULL )
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
    _setActiveOperation( _createKeysAndCertOperationIndex, &callbackInfo );

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
    status = _timedWaitForServerResponse( _createKeysAndCertOperationIndex,
                                          timeoutMs );

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

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

AwsIotProvisioningError_t AwsIotProvisioning_CreateCertificateFromCsr( IotMqttConnection_t connection,
                                                                       IotMqttQos_t operationQos,
                                                                       const char * pCertificateSigningRequest,
                                                                       size_t csrLength,
                                                                       uint32_t timeoutMs,
                                                                       const AwsIotProvisioningCreateCertFromCsrCallbackInfo_t * pResponseCallback )
{
    /* Make sure that the maximum MQTT response topic length is larger than the
     * topic filter  string that we initialize the topic buffer with. */
    AwsIotProvisioning_Assert(
        PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_MAX_TOPIC_LENGTH >
        strlen( PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_TOPIC_FILTER ) );

    char responseTopicsBuffer[ PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_MAX_TOPIC_LENGTH ] =
        PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_TOPIC_FILTER;
    IotMqttError_t mqttOpResult = IOT_MQTT_SUCCESS;
    /* Configuration for subscribing and unsubscribing to/from response topics. */
    AwsIotSubscriptionInfo_t responseSubscription =
    {
        .mqttConnection        = connection,
        .callbackFunction      = _csrResponseReceivedCallback,
        .timeout               = _AwsIotProvisioningMqttTimeoutMs,
        .pTopicFilterBase      = responseTopicsBuffer,
        .topicFilterBaseLength = PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_TOPIC_FILTER_LENGTH
    };
    size_t payloadSize = 0;
    uint8_t * pPayloadBuffer = NULL;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    /* Verify that library has been initialized. */
    AwsIotProvisioning_Assert( _checkInit() == true );

    if( connection == NULL )
    {
        IotLogError( "Bad parameter: MQTT connection is not initialized: Operation={\"%s\"}",
                     CREATE_CERT_FROM_CSR_OPERATION_LOG );

        status = AWS_IOT_PROVISIONING_BAD_PARAMETER;
    }
    else if( ( pCertificateSigningRequest == NULL ) || ( csrLength == 0 ) )
    {
        IotLogError( "Bad parameter: Invalid Certificate-Signing Request: "
                     "Operation={\"%s\"}", CREATE_CERT_FROM_CSR_OPERATION_LOG );

        status = AWS_IOT_PROVISIONING_BAD_PARAMETER;
    }
    /* Check that a callback function object along with a valid callback functor is provided. */
    else if( ( pResponseCallback == NULL ) ||
             ( pResponseCallback->function == NULL ) )
    {
        IotLogError(
            "Bad parameter: Invalid callback provided: Operation={\"%s\"}",
            CREATE_CERT_FROM_CSR_OPERATION_LOG );

        status = AWS_IOT_PROVISIONING_BAD_PARAMETER;
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Subscribe to the MQTT response topics. */
        mqttOpResult = AwsIot_ModifySubscriptions( IotMqtt_SubscribeSync, &responseSubscription );

        if( mqttOpResult != IOT_MQTT_SUCCESS )
        {
            IotLogError( "Failed to subscribe to response topics: TopicFilter={%s}, "
                         "Operation={\"%s\"}, MQTTError={%s}",
                         PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_TOPIC_FILTER,
                         CREATE_CERT_FROM_CSR_OPERATION_LOG,
                         IotMqtt_strerror( mqttOpResult ) );
            status = AWS_IOT_PROVISIONING_MQTT_ERROR;
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        IotLogDebug( "Subscribed to response topics: TopicFilter={%s}, Operation={\"%s\"}",
                     PROVISIONING_CREATE_CERT_FROM_CSR_RESPONSE_TOPIC_FILTER,
                     CREATE_CERT_FROM_CSR_OPERATION_LOG );

        /* Update the operation object to represent an active "Certificate-Signing Request" operation. */
        _provisioningCallbackInfo_t callbackInfo;
        callbackInfo.createCertFromCsrCallback = *pResponseCallback;
        _setActiveOperation( _createCertFromCsrOperationIndex, &callbackInfo );

        /* Serialization of request payload occurs in a 2-step process, one for
         * calculation of buffer size, and the next, serialization in allocated buffer. */
        /* Dry run serialization */
        status = _AwsIotProvisioning_CalculateCertFromCsrPayloadSize( pCertificateSigningRequest,
                                                                      csrLength,
                                                                      &payloadSize );

        if( status != AWS_IOT_PROVISIONING_SUCCESS )
        {
            IotLogError( "Unable to create PUBLISH payload: Failed to calculate size of payload: "
                         "Operation={\"%s\"}", CREATE_CERT_FROM_CSR_OPERATION_LOG );
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        AwsIotProvisioning_Assert( payloadSize != 0 );

        /* Allocate memory for payload buffer based on calculated serialization size. */
        pPayloadBuffer = AwsIotProvisioning_MallocPayload( payloadSize );

        if( pPayloadBuffer == NULL )
        {
            IotLogError( "Unable to create PUBLISH payload: Memory allocation for payload failed: "
                         "Operation={\"%s\"}",
                         REGISTER_THING_OPERATION_LOG );
            status = AWS_IOT_PROVISIONING_NO_MEMORY;
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Actual serialization in payload buffer. */
        status = _AwsIotProvisioning_SerializeCreateCertFromCsrRequestPayload( pCertificateSigningRequest,
                                                                               csrLength,
                                                                               pPayloadBuffer,
                                                                               payloadSize );

        if( status != AWS_IOT_PROVISIONING_SUCCESS )
        {
            IotLogError( "Unable to PUBLISH to request topic: Failed to serialize PUBLISH payload in buffer: "
                         "Operation={\"%s\"}",
                         CREATE_CERT_FROM_CSR_OPERATION_LOG );
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        publishInfo.qos = operationQos;
        publishInfo.pPayload = pPayloadBuffer;
        publishInfo.payloadLength = payloadSize;

        /* Set the operation topic name. */
        publishInfo.pTopicName = PROVISIONING_CREATE_CERT_FROM_CSR_REQUEST_TOPIC;
        publishInfo.topicNameLength = PROVISIONING_CREATE_CERT_FROM_CSR_REQUEST_TOPIC_LENGTH;

        IotLogDebug( "About to send request to server. Topic={%.*s}, Operation={\"%s\"}",
                     publishInfo.topicNameLength,
                     publishInfo.pTopicName,
                     CREATE_CERT_FROM_CSR_OPERATION_LOG );

        /* Publish to the Provisioning topic name. */
        mqttOpResult = IotMqtt_PublishSync( connection,
                                            &publishInfo,
                                            0,
                                            _AwsIotProvisioningMqttTimeoutMs );

        if( mqttOpResult != IOT_MQTT_SUCCESS )
        {
            IotLogError( "Failed to PUBLISH to request topic: "
                         "Topic={%.*s}, Operation={\"%s\"}, MQTTError={%s}",
                         publishInfo.topicNameLength,
                         publishInfo.pTopicName,
                         CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG,
                         IotMqtt_strerror( mqttOpResult ) );
            status = AWS_IOT_PROVISIONING_MQTT_ERROR;
        }
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        IotLogDebug( "Published to request topic: Operation={\"%s\"}",
                     CREATE_CERT_FROM_CSR_OPERATION_LOG );

        /* Wait for response from server using the given timeout period. */
        status = _timedWaitForServerResponse( _createCertFromCsrOperationIndex,
                                              timeoutMs );

        if( status == AWS_IOT_PROVISIONING_TIMEOUT )
        {
            IotLogDebug( "Operation timed out waiting for server response: Operation={\"%s\"}",
                         CREATE_CERT_FROM_CSR_OPERATION_LOG );
        }

        /* Unsubscribe from the MQTT response topics only if subscription to those topics was successful. */
        AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                    &responseSubscription );

        AwsIotProvisioning_FreePayload( pPayloadBuffer );
    }

    IotLogInfo( "Operation is complete: Operation={\"%s\"}",
                CREATE_CERT_FROM_CSR_OPERATION_LOG );

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

    if( provisioningConnection == NULL )
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
    _setActiveOperation( _registerThingOperationIndex, &callbackInfo );

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
    status = _timedWaitForServerResponse( _registerThingOperationIndex,
                                          timeoutMs );

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

        /* Clean-up all objeration objects. */
        _cleanUpOperationObject( _createKeysAndCertOperationIndex );
        _cleanUpOperationObject( _createCertFromCsrOperationIndex );
        _cleanUpOperationObject( _registerThingOperationIndex );

        IotLogInfo( "api: Completed cleanup of library." );
    }
    else
    {
        IotLogWarn( "api: Unexpected call to clean-up library: "
                    "Library is NOT initialized." );
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
