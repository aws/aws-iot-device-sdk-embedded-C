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
 * @file iot_mqtt_api.c
 * @brief Implements most user-facing functions of the Onboarding library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Error handling include. */
#include "iot_error.h"

/* Onboarding internal include. */
#include "private/aws_iot_onboarding_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"
#include "iot_atomic.h"

/* MQTT API include */
#include "iot_mqtt.h"

/* Helper AWS */
#include "aws_iot.h"

/* Logging module */
#include "iot_logging_setup.h"

/* Validate Onboarding configuration settings. */
#if AWS_IOT_ONBOARDING_ENABLE_ASSERTS != 0 && AWS_IOT_ONBOARDING_ENABLE_ASSERTS != 1
    #error "AWS_IOT_ONBOARDING_ENABLE_ASSERTS must be 0 or 1."
#endif
#if AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS <= 0
    #error "AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS cannot be 0 or negative."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Pointer to the encoder utility that will be used for serialization
 * of payload data in the library.
 */
static const IotSerializerEncodeInterface_t * _pAwsIotOnboardingEncoder = NULL;

/**
 * @brief Pointer to the decoder utility that will be used for de-serialization
 * of payload data in the library.
 */
static const IotSerializerDecodeInterface_t * _pAwsIotOnboardingDecoder = NULL;

/**
 * @brief The active Onboarding operation object.
 */
static _onboardingOperation_t _activeOperation;

/**
 * @brief Timeout for MQTT operations (that are required within the Onboarding operations).
 */
uint32_t _AwsIotOnboardingMqttTimeoutMs = AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS;

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief Printable names for each of the Onboarding operations.
 */
    static const char * _pGetDeviceCredentialsOperationName = "GET DEVICE CREDENTIALS";
    static const char * _pGetOnboardDeviceOperationName = "ONBOARD DEVICE";
#endif /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */

/*------------------------------------------------------------------*/

/**
 * @brief Parses the response from the server for device credentials, and invokes the provided user-callback with parsed
 * credentials, if successful.
 *
 * @param[in] pDeviceCredentialsResponse The response payload from the server to parse.
 * @param[in] deviceCredentialsResponseLength The length of the response payload.
 * @param[in] userCallback The user-provided callback to invoke on successful parsing of response.
 */
static AwsIotOnboardingError_t _parseDeviceCredentialsResponse( const
                                                                void * pDeviceCredentialsResponse,
                                                                size_t
                                                                deviceCredentialsResponseLength,
                                                                const AwsIotOnboardingCallbackInfo_t
                                                                * userCallbackInfo );

/**
 * @brief A utility common for processing server responses of all Onboarding operation APIs.
 * If there is an ongoing operation, the utility processes the incoming PUBLISH message and invokes the provided parser
 * if the server response is received on the "accepted" topic.
 *
 * @param[in] pPublishData The incoming PUBLISH message information from the server.
 * @param[in] responseParser The functor to invoke for parsing a successful server response payload.
 */
static void _commonServerResponseHandler( IotMqttCallbackParam_t * const pPublishData,
                                          _onboardingServerResponseParser responseParser );


/**
 * @brief The MQTT subscription callback for the request to GetDeviceCredentials Onboarding service API.
 */
static void _deviceCredentialsResponseReceivedCallback( void * param1,
                                                        IotMqttCallbackParam_t * const pPublish );

/**
 * @brief Resets the active operation object.
 * @note This function should be called ONLY if the operation object mutex is not destroyed.
 */
static void _resetActiveOperationData();

/*------------------------------------------------------------------*/
AwsIotOnboardingError_t _parseDeviceCredentialsResponse( const void * pDeviceCredentialsResponse,
                                                         size_t deviceCredentialsResponseLength,
                                                         const AwsIotOnboardingCallbackInfo_t *
                                                         userCallbackInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );
    AwsIotOnboardingCallbackParam_t userCallbackParam =
    {
        .callbackType = ( AwsIotOnboardingCallbackType_t ) 0
    };
    /** TODO - Move parsing logic into separate file for separate dependency and ease of testability **/
    IotSerializerDecoderObject_t payloadDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certificatePemDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certificateIdDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t privateKeyDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    if( _pAwsIotOnboardingDecoder->init( &payloadDecoder,
                                         pDeviceCredentialsResponse,
                                         deviceCredentialsResponseLength ) !=
        IOT_SERIALIZER_SUCCESS )
    {
        /* Decoder object initialization failed */
        IotLogError(
            "Could not initialize decoder for parsing response from server of %s operation.",
            _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    if( payloadDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
    {
        IotLogError(
            "Invalid container type of response received from server of %s operation. Payload should be of map type.",
            _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                         ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
                                         &certificatePemDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Cannot find "certificatePem" */
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
                     _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( certificatePemDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is text string.",
            ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
            _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                         ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
                                         &certificateIdDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Cannot find "certificateId" */
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
                     _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( certificateIdDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is text string.",
            ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
            _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                         ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
                                         &privateKeyDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Cannot find "private key" */
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
                     _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( privateKeyDecoder.type != IOT_SERIALIZER_SCALAR_BYTE_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" data in server response of %s operation. Expected type is byte string.",
            ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
            _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    /* Populate the data to be passed to the user callback.*/
    userCallbackParam.callbackType = AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE;
    userCallbackParam.u.deviceCredentialsInfo.pDeviceCertificate = ( const char * )
                                                                   certificatePemDecoder.u.value.u.string.pString;
    userCallbackParam.u.deviceCredentialsInfo.deviceCertificateLength =
        certificatePemDecoder.u.value.u.string.length;
    userCallbackParam.u.deviceCredentialsInfo.pCertificateId = ( const char * )
                                                               certificateIdDecoder.u.value.u.string.pString;
    userCallbackParam.u.deviceCredentialsInfo.certificateIdLength =
        certificateIdDecoder.u.value.u.string.length;
    userCallbackParam.u.deviceCredentialsInfo.pPrivateKey = ( const char * )
                                                            privateKeyDecoder.u.value.u.string.pString;
    userCallbackParam.u.deviceCredentialsInfo.privateKeyLength =
        privateKeyDecoder.u.value.u.string.length;

    /* Invoke the user-provided callback with the parsed credentials data . */
    userCallbackInfo->function( userCallbackInfo->userParam, &userCallbackParam );

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != AWS_IOT_ONBOARDING_INTERNAL_FAILURE )
    {
        _pAwsIotOnboardingDecoder->destroy( &payloadDecoder );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

void _commonServerResponseHandler( IotMqttCallbackParam_t * const pPublishData,
                                   _onboardingServerResponseParser responseParser )
{
    AwsIotStatus_t operationStatus = AWS_IOT_UNKNOWN;

    /* Determine whether the mutex is still valid (i.e. not destroyed) based on the reference count. If the mutex is
     * valid, indicate that we will be accessing the mutex by incrementing the reference count.
     * This tackles the RACE CONDITION with the possible cleanup of the mutex in the thread executing an Onboarding
     * Library API.*/
    if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) > 0 )
    {
        /* We will use a non-blocking mutex acquiring call to account for scenario
         * when server response is received after the mutex is destroyed
         * and thus, no longer valid. */
        if( IotMutex_TryLock( &_activeOperation.lock ) == true )
        {
            /* Is a user thread waiting for the result? */
            if( _activeOperation.info.userCallback.function == NULL )
            {
                IotLogDebug( "Received unexpected server response on topic %s.",
                             pPublishData->u.message.pTopicFilter,
                             pPublishData->u.message.topicFilterLength );
            }
            else
            {
                /* Determine whether the response from the server is "accepted" or "rejected". */
                operationStatus = AwsIot_ParseStatus( pPublishData->u.message.pTopicFilter,
                                                      pPublishData->u.message.topicFilterLength );

                switch( operationStatus )
                {
                    case AWS_IOT_ACCEPTED:
                        /* Parse the server response and execute the user callback. */
                        _activeOperation.info.status = responseParser(
                            pPublishData->u.message.info.pPayload,
                            pPublishData->u.message.info.payloadLength,
                            &_activeOperation.info.userCallback );

                        break;

                    case AWS_IOT_REJECTED:
                        _activeOperation.info.status = AWS_IOT_ONBOARDING_SERVER_REFUSED;
                        break;

                    default:
                        IotLogWarn( "Unknown parsing status on topic %s. Ignoring message.",
                                    pPublishData->u.message.pTopicFilter,
                                    pPublishData->u.message.topicFilterLength );
                        _activeOperation.info.status = AWS_IOT_ONBOARDING_INTERNAL_FAILURE;
                        break;
                }

                /* Notify the waiting thread about arrival of response from server */
                /* Increment the number of PUBLISH messages received. */
                IotSemaphore_Post( &_activeOperation.responseReceivedSem );

                /* Invalidate the user-callback information to prevent re-processing the response
                 * if we receive the same response multiple times (which is possible for a QoS 1 publish
                 * from the server). This is done to post on the semaphore ONLY ONCE on receiving the
                 * response from the server.*/
                _activeOperation.info.userCallback.userParam = NULL;
                _activeOperation.info.userCallback.function = NULL;
            }

            IotMutex_Unlock( &_activeOperation.lock );

            /* If no other thread/context is alive needing the mutex, then we will destroy it. */
            if( Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount ) == 1 )
            {
                IotMutex_Destroy( &_activeOperation.lock );
            }
        }
    }
    else
    {
        /* Reverse the previous increment operation as mutex is not valid. */
        Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
    }
}


/*-----------------------------------------------------------*/

void _deviceCredentialsResponseReceivedCallback( void * param1,
                                                 IotMqttCallbackParam_t * const pPublish )
{
    /* Silence warnings about unused variables.*/
    ( void ) param1;

    _commonServerResponseHandler( pPublish, _parseDeviceCredentialsResponse );
}

/*-----------------------------------------------------------*/

void _resetActiveOperationData()
{
    /* Determine whether the mutex is still valid (i.e. not destroyed) based on the reference count. If the mutex is
     * valid, indicate that we will be accessing the mutex by incrementing the reference count.*/
    if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) > 0 )
    {
        IotMutex_Lock( &( _activeOperation.lock ) );
        {
            _activeOperation.info.userCallback.userParam = NULL;
            _activeOperation.info.userCallback.function = NULL;
        }
        IotMutex_Unlock( &( _activeOperation.lock ) );

        IotSemaphore_TryWait( &_activeOperation.responseReceivedSem );
    }

    /* Reverse the previous increment operation as we don't need the mutex anymore. */
    ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
}

/*-----------------------------------------------------------*/

AwsIotOnboardingError_t AwsIotOnboarding_Init( uint32_t mqttTimeoutMs )
{
    bool mutexCreated = false;

    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );

    /* Get the pointers to the encoder function tables. */
    #if AWS_IOT_ONBOARDING_FORMAT == AWS_IOT_ONBOARDING_FORMAT_CBOR
        _pAwsIotOnboardingDecoder = IotSerializer_GetCborDecoder();
        _pAwsIotOnboardingEncoder = IotSerializer_GetCborEncoder();
    #else
    #error "AWS_IOT_ONBOARDING_FORMAT needs to be set."
    #endif

    /* Create the mutex guarding the operation object. */
    if( IotMutex_Create( &( _activeOperation.lock ), false ) == false )
    {
        IotLogError( "Failed to initialize Onboarding library due to mutex creation failure." );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INIT_FAILED );
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
                "Failed to init Onboarding library as mutex reference counter is in an invalid state." );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INIT_FAILED );
        }
    }

    /* Save the MQTT timeout option. */
    if( mqttTimeoutMs != 0 )
    {
        _AwsIotOnboardingMqttTimeoutMs = mqttTimeoutMs;
    }

    _resetActiveOperationData();

    /* Create a binary semaphore needed for signaling arrival of server responses. */
    if( IotSemaphore_Create( &( _activeOperation.responseReceivedSem ),
                             0 /* initialValue */,
                             1 /* maxValue */ ) == false )
    {
        IotLogError( "Failed to initialize Onboarding library due to semaphore creation failure." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INIT_FAILED );
    }

    IotLogInfo( "Onboarding library successfully initialized." );

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != AWS_IOT_ONBOARDING_SUCCESS )
    {
        if( mutexCreated )
        {
            IotMutex_Destroy( &_activeOperation.lock );
        }

        ( void ) Atomic_AND_u32( &_activeOperation.mutexReferenceCount, 0u );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

AwsIotOnboardingError_t AwsIotOnboarding_GetDeviceCredentials( IotMqttConnection_t
                                                               onboardingConnection,
                                                               uint32_t flags,
                                                               uint32_t timeoutMs,
                                                               const AwsIotOnboardingCallbackInfo_t * deviceCredentialsResponseCallback )
{
    bool mutexNotAvailableError = false;
    char responseTopicsBuffer[ ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_MAX_TOPIC_LENGTH ] =
    { 0 };
    IotMqttError_t mqttOpResult = IOT_MQTT_SUCCESS;
    /* Configuration for subscribing and unsubsubscribing to/from response topics. */
    AwsIotSubscriptionInfo_t responseSubscription =
    {
        .mqttConnection        = onboardingConnection,
        .callbackFunction      = _deviceCredentialsResponseReceivedCallback,
        .timeout               = _AwsIotOnboardingMqttTimeoutMs,
        .pTopicFilterBase      = responseTopicsBuffer,
        .topicFilterBaseLength = ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER_LENGTH
    };
    bool subscribedToResponseTopics = false;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    /* Suppress unused variable warning. */
    ( void ) flags;
    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );

    /* Increment the reference counter to indicate that mutex is required. */
    if( Atomic_Increment_u32( &_activeOperation.mutexReferenceCount ) == 0u )
    {
        IotLogError( "Mutex is unavailable for API operation." );
        mutexNotAvailableError = true;
        ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    /* Copy the response topics in a local buffer for appropriate suffixes to be added. */
    ( void ) memcpy( responseTopicsBuffer, ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER,
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER_LENGTH );

    if( onboardingConnection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_PARAMETER );
    }

    /* Check that a callback function object along with a valid callback functor is provided. */
    if( ( deviceCredentialsResponseCallback == NULL ) ||
        ( deviceCredentialsResponseCallback->function == NULL ) )
    {
        IotLogError(
            "Invalid callback provided. Both the callback object and functor within should be provided to the %s operation",
            _pGetDeviceCredentialsOperationName );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_PARAMETER );
    }

    /* Subscribe to the MQTT response topics. */
    mqttOpResult = AwsIot_ModifySubscriptions( IotMqtt_SubscribeSync, &responseSubscription );

    if( mqttOpResult != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Unable to subscribe to response topics for %s operation",
                     _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_MQTT_ERROR );
    }
    else
    {
        subscribedToResponseTopics = true;
    }

    /* Increment the reference count as we will be acquiring the mutex. */
    ( void ) Atomic_Increment_u32( &_activeOperation.mutexReferenceCount );

    /* Update shared active operation object to indicate that an operation is in
     * progress. */
    IotMutex_Lock( &( _activeOperation.lock ) );
    {
        /* If a successful response is not received, it should be treated as
         * MQTT error. */
        _activeOperation.info.status = AWS_IOT_ONBOARDING_MQTT_ERROR;

        /* Store the user supplied callback. */
        _activeOperation.info.userCallback.function =
            deviceCredentialsResponseCallback->function;
        _activeOperation.info.userCallback.userParam =
            deviceCredentialsResponseCallback->userParam;
    }
    IotMutex_Unlock( &( _activeOperation.lock ) );
    /* Decrement the reference count as we have released the mutex. */
    ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );

    /* Onboarding already has an acknowledgement mechanism, so sending the message at
     * QoS 1 provides no benefit. */
    publishInfo.qos = IOT_MQTT_QOS_0;

    /* Set the payload as the Onboarding request. */
    publishInfo.pPayload = NULL;
    publishInfo.payloadLength = 0u;

    /* Set the operation topic name. */
    publishInfo.pTopicName = ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC;
    publishInfo.topicNameLength = ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC_LENGTH;

    IotLogDebug( "Onboarding %s message will be published to topic %.*s",
                 _pGetDeviceCredentialsOperationName,
                 publishInfo.topicNameLength,
                 publishInfo.pTopicName );

    /* Publish to the Onboarding topic name. */
    mqttOpResult = IotMqtt_PublishSync( onboardingConnection,
                                        &publishInfo,
                                        0,
                                        _AwsIotOnboardingMqttTimeoutMs );

    if( mqttOpResult != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Unable to subscribe to response topics for %s operation",
                     _pGetDeviceCredentialsOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_MQTT_ERROR );
    }

    /* Wait for response from the server. */
    if( IotSemaphore_TimedWait( &_activeOperation.responseReceivedSem,
                                timeoutMs ) == false )
    {
        status = AWS_IOT_ONBOARDING_TIMEOUT;
    }

    /* There can be an edge case of receiving the server response right after the timeout has occured.
     * If such an edge case has occured and is causing the subscription callback is to currently execute,
     * we will void the "timeout" resolution and instead use the outcome of the callback execution.
     * Rationale - This API is not intended to have an "exact" implementation of server timeout, as completing
     * the operation is more valuable for the customer. */
    IotMutex_Lock( &_activeOperation.lock );

    /* Check if we hit the edge case of a race condition between receiving the server response and the timer firing . */
    if( _activeOperation.info.status != AWS_IOT_ONBOARDING_MQTT_ERROR )
    {
        status = _activeOperation.info.status;
    }

    IotMutex_Unlock( &_activeOperation.lock );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Unsubscibe from the MQTT response topics only if subscription to those topics was successful. */
    if( subscribedToResponseTopics )
    {
        AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                    &responseSubscription );
    }

    if( !mutexNotAvailableError )
    {
        /* Reset the active operation */
        _resetActiveOperationData();

        /* Indicate that the mutex is no longer required by the API as its execution lifetime is ending. */
        ( void ) Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/


AwsIotOnboardingError_t AwsIotOnboarding_OnboardDevice( IotMqttConnection_t onboardingConnection,
                                                        const AwsIotOnboardingOnboardDeviceInfo_t * pOnboardingDataInfo,
                                                        uint32_t timeoutMs,
                                                        const AwsIotOnboardingCallbackInfo_t * responseCallback )
{
    ( void ) onboardingConnection;
    ( void ) pOnboardingDataInfo;
    ( void ) timeoutMs;
    ( void ) responseCallback;

    return AWS_IOT_ONBOARDING_SUCCESS;
}

/*-----------------------------------------------------------*/

void AwsIotOnboarding_Cleanup( void )
{
    _AwsIotOnboardingMqttTimeoutMs = AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS;

    _resetActiveOperationData();

    /* We will destroy the mutex only if there is no other thread/context alive that needs the mutex.
     * This tackles the race condition with the execution of an MQTT callback (that was registered by the operation
     * APIs) accessing the mutex.*/
    if( Atomic_Decrement_u32( &_activeOperation.mutexReferenceCount ) == 1 )
    {
        IotMutex_Destroy( &( _activeOperation.lock ) );
    }

    IotSemaphore_Destroy( &( _activeOperation.responseReceivedSem ) );

    IotLogInfo( "Onboarding library cleanup done." );
}

/*-----------------------------------------------------------*/

const char * AwsIotOnboarding_strerror( AwsIotOnboardingError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case AWS_IOT_ONBOARDING_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case AWS_IOT_ONBOARDING_INIT_FAILED:
            pMessage = "INIT FAILED";
            break;

        case AWS_IOT_ONBOARDING_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case AWS_IOT_ONBOARDING_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case AWS_IOT_ONBOARDING_MQTT_ERROR:
            pMessage = "MQTT ERROR";
            break;

        case AWS_IOT_ONBOARDING_SERVER_REFUSED:
            pMessage = "SERVER REFUSED";
            break;

        case AWS_IOT_ONBOARDING_BAD_RESPONSE:
            pMessage = "BAD RESPONSE";
            break;

        case AWS_IOT_ONBOARDING_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case AWS_IOT_ONBOARDING_INTERNAL_FAILURE:
            pMessage = "FAILED: INTERNAL FAILURE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/
