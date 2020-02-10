/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_tests_mqtt_platform.c
 * @brief Tests interaction of MQTT with the lower layers, such as network and task pool.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* SDK initialization include. */
#include "iot_init.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* MQTT lightweight includes. */
#include "iot_mqtt_protocol.h"
#include "iot_mqtt_lightweight.h"

/* Allow these tests to manipulate the task pool and create failures by including
 * the task pool internal header. */
#undef LIBRARY_LOG_LEVEL
#undef LIBRARY_LOG_NAME
#include "../src/private/iot_taskpool_internal.h"

/* MQTT test access include. */
#include "iot_test_access_mqtt.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

/* Test network header include. */
#include IOT_TEST_NETWORK_HEADER

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Timeout to use for the tests. This can be short, but should allow time
 * for other threads to run.
 */
#define TIMEOUT_MS                  ( 400 )

/*
 * Client identifier and length to use for the MQTT API tests.
 */
#define CLIENT_IDENTIFIER           ( "test" )                                           /**< @brief Client identifier. */
#define CLIENT_IDENTIFIER_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) ) /**< @brief Length of client identifier. */

/**
 * @brief A non-NULL function pointer to use for subscription callback. This
 * "function" should cause a crash if actually called.
 */
#define SUBSCRIPTION_CALLBACK_FUNCTION \
    ( ( void ( * )( void *,            \
                    IotMqttCallbackParam_t * ) ) 0x1 )

/**
 * @brief Length of an arbitrary packet for testing. A buffer will be allocated
 * for it, but its contents don't matter.
 */
#define PACKET_LENGTH          ( 1 )

/**
 * @brief A short keep-alive interval to use for the keep-alive tests. It may be
 * shorter than the minimum 1 second specified by the MQTT spec.
 */
#define SHORT_KEEP_ALIVE_MS    ( 100 )

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values of test configuration constants.
 */
#ifndef IOT_TEST_MQTT_TIMEOUT_MS
    #define IOT_TEST_MQTT_TIMEOUT_MS             ( 5000 )
#endif
#ifndef IOT_TEST_MQTT_CONNECT_RETRY_COUNT
    #define IOT_TEST_MQTT_CONNECT_RETRY_COUNT    ( 1 )
#endif
#ifndef IOT_TEST_MQTT_PUBLISH_RETRY_COUNT
    #define IOT_TEST_MQTT_PUBLISH_RETRY_COUNT    ( 3 )
#endif
/** @endcond */

#if IOT_TEST_MQTT_CONNECT_RETRY_COUNT < 1
    #error "IOT_TEST_MQTT_CONNECT_RETRY_COUNT must be at least 1."
#endif
#if IOT_TEST_MQTT_PUBLISH_RETRY_COUNT < 0
    #error "IOT_TEST_MQTT_CONNECT_RETRY_COUNT must be at least 0."
#endif

/**
 * @brief Determine which MQTT server mode to test (AWS IoT or Mosquitto).
 */
#if !defined( IOT_TEST_MQTT_MOSQUITTO ) || IOT_TEST_MQTT_MOSQUITTO == 0
    #define AWS_IOT_MQTT_SERVER    true
#else
    #define AWS_IOT_MQTT_SERVER    false
#endif

/**
 * @brief The maximum length of an MQTT client identifier.
 *
 * When @ref IOT_TEST_MQTT_CLIENT_IDENTIFIER is defined, this value must
 * accommodate the length of @ref IOT_TEST_MQTT_CLIENT_IDENTIFIER plus 4
 * to accommodate the Last Will and Testament test. Otherwise, this value is
 * set to 24, which is the longest client identifier length an MQTT server is
 * obligated to accept plus a NULL terminator.
 */
#ifdef IOT_TEST_MQTT_CLIENT_IDENTIFIER
    #define CLIENT_IDENTIFIER_MAX_LENGTH    ( sizeof( IOT_TEST_MQTT_CLIENT_IDENTIFIER ) + 4 )
#else
    #define CLIENT_IDENTIFIER_MAX_LENGTH    ( 24 )
#endif

/**
 * @brief Generates a topic by suffixing the client identifier with a suffix.
 *
 * @param[in] bufferName The name of the buffer for the topic.
 * @param[in] suffix The suffix to place at the end of the client identifier.
 */
#define GENERATE_TOPIC_WITH_SUFFIX( bufferName, suffix )                        \
    char bufferName[ CLIENT_IDENTIFIER_MAX_LENGTH + sizeof( suffix ) ] = { 0 }; \
    ( void ) snprintf( bufferName,                                              \
                       CLIENT_IDENTIFIER_MAX_LENGTH + sizeof( suffix ),         \
                       "%s%s",                                                  \
                       _pClientIdentifier,                                      \
                       suffix );

/*
 * Will topic name and length to use for the MQTT API tests.
 */
#define TEST_TOPIC_NAME             ( "/test/topic" )                                  /**< @brief An arbitrary topic name. */
#define TEST_TOPIC_NAME_LENGTH      ( ( uint16_t ) ( sizeof( TEST_TOPIC_NAME ) - 1 ) ) /**< @brief Length of topic name. */

/*
 * Constants that affect the behavior of #TEST_MQTT_Unit_API_PublishDuplicates.
 */
#define DUP_CHECK_RETRY_MS         ( 100 )  /**< @brief When to start sending duplicate packets. */
#define DUP_CHECK_RETRY_LIMIT      ( 3 )    /**< @brief How many duplicate packets to send. */
#define DUP_CHECK_TIMEOUT          ( 3000 ) /**< @brief Total time allowed to send all duplicate packets.
                                             * Duplicates are sent using an exponential backoff strategy. */

/*-----------------------------------------------------------*/

/**
 * @brief An #IotMqttNetworkInfo_t to share among the tests.
 */
static IotMqttNetworkInfo_t _networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief An #IotNetworkInterface_t to share among the tests.
 */
static IotNetworkInterface_t _networkInterface = { 0 };

/**
 * @brief An MQTT connection to share among the tests.
 */
static IotMqttConnection_t _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/**
 * @brief An #IotMqttNetworkInfo_t to use for the re-entrancy tests.
 */
static IotMqttNetworkInfo_t _reentrantNetworkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief Network server info to use for the re-entrancy tests.
 */
static const struct IotNetworkServerInfo _serverInfo = IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER;

/**
 * @brief Network credential info to use for the re-entrancy tests.
 */
#if IOT_TEST_SECURED_CONNECTION == 1
    static const struct IotNetworkCredentials _credentials = IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER;
#endif

#ifdef IOT_TEST_MQTT_SERIALIZER

/**
 * @brief Provide a pointer to a serializer that may be overridden.
 */
    static const IotMqttSerializer_t * _pMqttSerializer = NULL;
#else

/**
 * @brief Function pointers to the default MQTT serializers.
 */
    static const IotMqttSerializer_t _mqttSerializer =
    {
        .getPacketType      = _IotMqtt_GetPacketType,
        .getRemainingLength = _IotMqtt_GetRemainingLength,
        .freePacket         = _IotMqtt_FreePacket,
        .serialize          =
        {
            .connect        = _IotMqtt_SerializeConnect,
            .publish        = _IotMqtt_SerializePublish,
            .publishSetDup  = _IotMqtt_PublishSetDup,
            .puback         = _IotMqtt_SerializePuback,
            .subscribe      = _IotMqtt_SerializeSubscribe,
            .unsubscribe    = _IotMqtt_SerializeUnsubscribe,
            .pingreq        = _IotMqtt_SerializePingreq,
            .disconnect     = _IotMqtt_SerializeDisconnect
        },
        .deserialize        =
        {
            .connack        = _IotMqtt_DeserializeConnack,
            .publish        = _IotMqtt_DeserializePublish,
            .puback         = _IotMqtt_DeserializePuback,
            .suback         = _IotMqtt_DeserializeSuback,
            .unsuback       = _IotMqtt_DeserializeUnsuback,
            .pingresp       = _IotMqtt_DeserializePingresp
        }
    };

/**
 * @brief The MQTT serializers to use in these tests.
 */
    static const IotMqttSerializer_t * _pMqttSerializer = &_mqttSerializer;
#endif /* ifdef IOT_TEST_MQTT_SERIALIZER_INITIALIZER */

/*
 * Return values of the mocked network functions.
 */
static IotNetworkError_t _createStatus = IOT_NETWORK_SUCCESS;             /**< @brief Return value for #_networkCreate. */
static IotNetworkError_t _setReceiveCallbackStatus = IOT_NETWORK_SUCCESS; /**< @brief Return value for #_networkSetReceiveCallback. */
static IotNetworkError_t _sendStatus = IOT_NETWORK_SUCCESS;               /**< @brief Return value for #_networkSend. */
static IotNetworkError_t _closeStatus = IOT_NETWORK_SUCCESS;              /**< @brief Return value for #_networkClose. */
static IotNetworkError_t _destroyStatus = IOT_NETWORK_SUCCESS;            /**< @brief Return value for #_networkDestroy. */

/**
 * @brief Filler text to publish.
 */
static const char _pSamplePayload[] =
    "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor"
    " incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis "
    "nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. "
    "Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu"
    " fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in"
    " culpa qui officia deserunt mollit anim id est laborum."
    "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor"
    " incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis "
    "nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. "
    "Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu"
    " fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in"
    " culpa qui officia deserunt mollit anim id est laborum.";

/**
 * @brief Length of #_pSamplePayload.
 */
static const size_t _samplePayloadLength = sizeof( _pSamplePayload ) - 1;

/**
 * @brief Buffer holding the client identifier used for the tests.
 */
static char _pClientIdentifier[ CLIENT_IDENTIFIER_MAX_LENGTH ] = { 0 };

/*-----------------------------------------------------------*/

/**
 * @brief Establish an MQTT connection. Retry if enabled.
 */
static IotMqttError_t _mqttConnect( const IotMqttNetworkInfo_t * pNetworkInfo,
                                    const IotMqttConnectInfo_t * pConnectInfo,
                                    uint32_t timeoutMs,
                                    IotMqttConnection_t * const pMqttConnection )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    int32_t retryCount = 0;

    for( ; retryCount < IOT_TEST_MQTT_CONNECT_RETRY_COUNT; retryCount++ )
    {
        status = IotMqtt_Connect( pNetworkInfo, pConnectInfo, timeoutMs, pMqttConnection );

        #if ( IOT_TEST_MQTT_CONNECT_RETRY_COUNT > 1 )
            if( ( status == IOT_MQTT_NETWORK_ERROR ) || ( status == IOT_MQTT_TIMEOUT ) )
            {
                /* AWS IoT Service limits only allow 1 connection per MQTT client ID per second.
                 * Initially wait until 1100 ms have elapsed since the last connection, then
                 * increase exponentially. */
                IotClock_SleepMs( 1100 << retryCount );
            }
            else
            {
                break;
            }
        #endif
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Mocked network create function.
 */
static IotNetworkError_t _networkCreate( IotNetworkServerInfo_t pServerInfo,
                                         IotNetworkCredentials_t pCredentialInfo,
                                         IotNetworkConnection_t * pConnection )
{
    ( void ) pServerInfo;
    ( void ) pCredentialInfo;

    *pConnection = NULL;

    return _createStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Mocked network set receive callback function.
 */
static IotNetworkError_t _networkSetReceiveCallback( IotNetworkConnection_t pConnection,
                                                     IotNetworkReceiveCallback_t receiveCallback,
                                                     void * pContext )
{
    ( void ) pConnection;
    ( void ) receiveCallback;
    ( void ) pContext;

    return _setReceiveCallbackStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Mocked network send function.
 */
static size_t _networkSend( IotNetworkConnection_t pConnection,
                            const uint8_t * pMessage,
                            size_t messageLength )
{
    size_t bytesSent = 0;

    ( void ) pConnection;
    ( void ) pMessage;

    if( _sendStatus == IOT_NETWORK_SUCCESS )
    {
        bytesSent = messageLength;
    }

    return bytesSent;
}

/*-----------------------------------------------------------*/

/**
 * @brief Mocked network close function.
 */
static IotNetworkError_t _networkClose( IotNetworkConnection_t pConnection )
{
    ( void ) pConnection;

    return _closeStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Mocked network destroy function.
 */
static IotNetworkError_t _networkDestroy( IotNetworkConnection_t pConnection )
{
    ( void ) pConnection;

    return _destroyStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Subscription callback function. Checks for valid parameters and unblocks
 * the main test thread.
 */
static void _publishReceived( void * pArgument,
                              IotMqttCallbackParam_t * pPublish )
{
    IotSemaphore_t * pWaitSem = ( IotSemaphore_t * ) pArgument;

    /* If the received messages matches what was sent, unblock the waiting thread. */
    if( ( pPublish->u.message.info.payloadLength == _samplePayloadLength ) &&
        ( strncmp( pPublish->u.message.info.pPayload,
                   _pSamplePayload,
                   _samplePayloadLength ) == 0 ) )
    {
        IotSemaphore_Post( pWaitSem );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief A subscription callback function that blocks on a semaphore until signaled.
 */
static void _blockingCallback( void * pArgument,
                               IotMqttCallbackParam_t * pPublish )
{
    IotSemaphore_t * pSemaphore = ( IotSemaphore_t * ) pArgument;

    /* Silence warnings about unused parameters. */
    ( void ) pPublish;

    /* Wait until signaled. */
    IotSemaphore_Wait( pSemaphore );
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback that makes additional MQTT API calls.
 */
static void _reentrantCallback( void * pArgument,
                                IotMqttCallbackParam_t * pOperation )
{
    bool status = true;
    IotMqttError_t mqttStatus = IOT_MQTT_STATUS_PENDING;
    IotSemaphore_t * pWaitSemaphores = ( IotSemaphore_t * ) pArgument;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttOperation_t unsubscribeOperation = IOT_MQTT_OPERATION_INITIALIZER;

    /* The topic to use for this test. */
    GENERATE_TOPIC_WITH_SUFFIX( pTopic, "/Reentrancy" );
    const uint16_t topicLength = ( uint16_t ) strlen( pTopic );

    publishInfo.qos = IOT_MQTT_QOS_1;
    publishInfo.pTopicName = pTopic;
    publishInfo.topicNameLength = topicLength;
    publishInfo.pPayload = _pSamplePayload;
    publishInfo.payloadLength = _samplePayloadLength;
    publishInfo.retryLimit = IOT_TEST_MQTT_PUBLISH_RETRY_COUNT;
    publishInfo.retryMs = IOT_TEST_MQTT_TIMEOUT_MS;

    mqttStatus = IotMqtt_PublishSync( pOperation->mqttConnection,
                                      &publishInfo,
                                      0,
                                      IOT_TEST_MQTT_TIMEOUT_MS );

    if( mqttStatus == IOT_MQTT_SUCCESS )
    {
        status = IotSemaphore_TimedWait( &( pWaitSemaphores[ 0 ] ),
                                         IOT_TEST_MQTT_TIMEOUT_MS );
    }
    else
    {
        status = false;
    }

    /* Remove subscription and disconnect. */
    if( status == true )
    {
        subscription.pTopicFilter = pTopic;
        subscription.topicFilterLength = topicLength;

        mqttStatus = IotMqtt_UnsubscribeAsync( pOperation->mqttConnection,
                                               &subscription,
                                               1,
                                               IOT_MQTT_FLAG_WAITABLE,
                                               NULL,
                                               &unsubscribeOperation );

        if( mqttStatus == IOT_MQTT_STATUS_PENDING )
        {
            /* Disconnect the MQTT connection. */
            IotMqtt_Disconnect( pOperation->mqttConnection, 0 );

            /* Waiting on an operation whose connection is closed should return
             * "Network Error". */
            mqttStatus = IotMqtt_Wait( unsubscribeOperation,
                                       500 );

            status = ( mqttStatus == IOT_MQTT_NETWORK_ERROR );
        }
        else
        {
            status = false;
        }
    }

    /* Disconnect and unblock the main test thread. */
    if( status == true )
    {
        IotSemaphore_Post( &( pWaitSemaphores[ 1 ] ) );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Serializer override for PUBACK that always fails.
 */
static IotMqttError_t _serializePuback( uint16_t packetIdentifier,
                                        uint8_t ** pPubackPacket,
                                        size_t * pPacketSize )
{
    ( void ) packetIdentifier;
    ( void ) pPubackPacket;
    ( void ) pPacketSize;

    return IOT_MQTT_NO_MEMORY;
}

/*-----------------------------------------------------------*/

/**
 * @brief Wait for a reference count to reach a target value, subject to a timeout.
 */
static bool _waitForCount( IotMutex_t * pMutex,
                           const int32_t * pReferenceCount,
                           int32_t target )
{
    bool status = false;
    int32_t referenceCount = 0;
    uint32_t sleepCount = 0;

    /* Calculate limit on the number of times to sleep for 100 ms. */
    const uint32_t sleepLimit = ( IOT_TEST_MQTT_TIMEOUT_MS / 100 ) +
                                ( ( IOT_TEST_MQTT_TIMEOUT_MS % 100 ) != 0 );

    /* Wait for the reference count to reach the target value. */
    for( sleepCount = 0; sleepCount < sleepLimit; sleepCount++ )
    {
        /* Read reference count. */
        IotMutex_Lock( pMutex );
        referenceCount = *pReferenceCount;
        IotMutex_Unlock( pMutex );

        /* Exit if target value is reached. Otherwise, sleep. */
        if( referenceCount == target )
        {
            status = true;
            break;
        }
        else
        {
            IotClock_SleepMs( 100 );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for MQTT platform tests.
 */
TEST_GROUP( MQTT_Unit_Platform );

/**
 * @brief Test group for MQTT platform tests requiring the network.
 */
TEST_GROUP( MQTT_System_Platform );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for MQTT platform tests.
 */
TEST_SETUP( MQTT_Unit_Platform )
{
    /* Reset the network info and interface. */
    ( void ) memset( &_networkInfo, 0x00, sizeof( IotMqttNetworkInfo_t ) );
    ( void ) memset( &_networkInterface, 0x00, sizeof( IotNetworkInterface_t ) );

    _createStatus = IOT_NETWORK_SUCCESS;
    _setReceiveCallbackStatus = IOT_NETWORK_SUCCESS;
    _sendStatus = IOT_NETWORK_SUCCESS;
    _closeStatus = IOT_NETWORK_SUCCESS;
    _destroyStatus = IOT_NETWORK_SUCCESS;

    _networkInterface.create = _networkCreate;
    _networkInterface.setReceiveCallback = _networkSetReceiveCallback;
    _networkInterface.send = _networkSend;
    _networkInterface.close = _networkClose;
    _networkInterface.destroy = _networkDestroy;

    _networkInfo.pNetworkInterface = &_networkInterface;

    /* Initialize libraries. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for MQTT system platform tests.
 */
TEST_SETUP( MQTT_System_Platform )
{
    /* Generate a new, unique client identifier based on the time if no client
     * identifier is defined. Otherwise, copy the provided client identifier. */
    #ifndef IOT_TEST_MQTT_CLIENT_IDENTIFIER
        ( void ) snprintf( _pClientIdentifier,
                           CLIENT_IDENTIFIER_MAX_LENGTH,
                           "iot%llu",
                           ( long long unsigned int ) IotClock_GetTimeMs() );
    #else
        ( void ) strncpy( _pClientIdentifier,
                          IOT_TEST_MQTT_CLIENT_IDENTIFIER,
                          CLIENT_IDENTIFIER_MAX_LENGTH );
    #endif

    /* Set the overrides for the default serializers. */
    #ifdef IOT_TEST_MQTT_SERIALIZER
        _pMqttSerializer = IOT_TEST_MQTT_SERIALIZER;
    #endif

    /* Set the MQTT network setup parameters. */
    ( void ) memset( &_reentrantNetworkInfo, 0x00, sizeof( IotMqttNetworkInfo_t ) );
    _reentrantNetworkInfo.createNetworkConnection = true;
    _reentrantNetworkInfo.u.setup.pNetworkServerInfo = ( void * ) &_serverInfo;
    _reentrantNetworkInfo.pNetworkInterface = IOT_TEST_NETWORK_INTERFACE;
    _reentrantNetworkInfo.pMqttSerializer = _pMqttSerializer;

    #if IOT_TEST_SECURED_CONNECTION == 1
        _reentrantNetworkInfo.u.setup.pNetworkCredentialInfo = ( void * ) &_credentials;
    #endif

    /* Initialize libraries. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );
    TEST_ASSERT_EQUAL( IOT_NETWORK_SUCCESS, IotTestNetwork_Init() );
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for MQTT platform tests.
 */
TEST_TEAR_DOWN( MQTT_Unit_Platform )
{
    IotMqtt_Cleanup();
    IotSdk_Cleanup();

    /* Clear the connection pointer. */
    _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for MQTT system platform tests.
 */
TEST_TEAR_DOWN( MQTT_System_Platform )
{
    IotMqtt_Cleanup();
    IotTestNetwork_Cleanup();
    IotSdk_Cleanup();

    /* Clear the connection pointer. */
    _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for MQTT platform tests.
 */
TEST_GROUP_RUNNER( MQTT_Unit_Platform )
{
    RUN_TEST_CASE( MQTT_Unit_Platform, ConnectNetworkFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, ConnectScheduleFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, DisconnectNetworkFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, PingreqSendFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, PublishScheduleFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, PublishRetryScheduleFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, PubackScheduleSerializeFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, SubscriptionScheduleFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, NotifyScheduleFailure );
    RUN_TEST_CASE( MQTT_Unit_Platform, SingleThreaded );
    RUN_TEST_CASE( MQTT_Unit_Platform, SubscriptionReferences );
    RUN_TEST_CASE( MQTT_Unit_Platform, SubscriptionListTooLarge );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for MQTT system platform tests.
 */
TEST_GROUP_RUNNER( MQTT_System_Platform )
{
    RUN_TEST_CASE( MQTT_System_Platform, SubscribeCompleteReentrancy );
    RUN_TEST_CASE( MQTT_System_Platform, IncomingPublishReentrancy );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_connect when the network fails.
 */
TEST( MQTT_Unit_Platform, ConnectNetworkFailure )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

    /* Set test client identifier. */
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

    /* Network connection creation failure. */
    _networkInfo.createNetworkConnection = true;
    _createStatus = IOT_NETWORK_FAILURE;
    status = IotMqtt_Connect( &_networkInfo, &connectInfo, TIMEOUT_MS, &mqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_NETWORK_ERROR, status );

    /* Set receive callback failure. */
    _createStatus = IOT_NETWORK_SUCCESS;
    _setReceiveCallbackStatus = IOT_NETWORK_FAILURE;
    status = IotMqtt_Connect( &_networkInfo, &connectInfo, TIMEOUT_MS, &mqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_NETWORK_ERROR, status );

    /* Failure in set receive callback, close, and destroy. */
    _closeStatus = IOT_NETWORK_FAILURE;
    _destroyStatus = IOT_NETWORK_FAILURE;
    status = IotMqtt_Connect( &_networkInfo, &connectInfo, TIMEOUT_MS, &mqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_NETWORK_ERROR, status );

    /* Failure to send MQTT Connect. */
    _setReceiveCallbackStatus = IOT_NETWORK_SUCCESS;
    _closeStatus = IOT_NETWORK_SUCCESS;
    _destroyStatus = IOT_NETWORK_SUCCESS;
    _sendStatus = IOT_NETWORK_FAILURE;
    status = IotMqtt_Connect( &_networkInfo, &connectInfo, TIMEOUT_MS, &mqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_NETWORK_ERROR, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_connect when the keep-alive
 * job fails to schedule.
 */
TEST( MQTT_Unit_Platform, ConnectScheduleFailure )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttConnection_t * pMqttConnection = NULL;

    /* Create a new MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 100 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Set an invalid status for the keep-alive job, preventing it from being
     * scheduled. */
    pMqttConnection->pingreq.jobStorage.status = IOT_TASKPOOL_STATUS_COMPLETED;
    status = IotTestMqtt_scheduleKeepAlive( pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_SCHEDULING_ERROR, status );

    /* Clean up. */
    pMqttConnection->references--;
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_disconnect when the network fails.
 */
TEST( MQTT_Unit_Platform, DisconnectNetworkFailure )
{
    _mqttConnection_t * pMqttConnection = NULL;

    /* Call disconnect with a failing send. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 100 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );
    _sendStatus = IOT_NETWORK_FAILURE;
    IotMqtt_Disconnect( pMqttConnection, 0 );
    _sendStatus = IOT_NETWORK_SUCCESS;

    /* Call disconnect with a failing close. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 100 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );
    _closeStatus = IOT_NETWORK_FAILURE;
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior when a PINGREQ cannot be sent.
 */
TEST( MQTT_Unit_Platform, PingreqSendFailure )
{
    _mqttConnection_t * pMqttConnection = NULL;

    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 1 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Set a short keep alive period and sleep for at least that period. Otherwise,
     * the PINGREQ will not be sent. */
    pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = SHORT_KEEP_ALIVE_MS;
    pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs = SHORT_KEEP_ALIVE_MS;
    IotClock_SleepMs( SHORT_KEEP_ALIVE_MS * 2 );

    _sendStatus = IOT_NETWORK_FAILURE;
    _IotMqtt_ProcessKeepAlive( IOT_SYSTEM_TASKPOOL, pMqttConnection->pingreq.job, pMqttConnection );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_publishasync when scheduling fails.
 */
TEST( MQTT_Unit_Platform, PublishScheduleFailure )
{
    IotMqttConnection_t pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotTaskPool_t taskPool = IOT_SYSTEM_TASKPOOL;
    IotMqttOperation_t publishOperation = IOT_MQTT_OPERATION_INITIALIZER;
    uint32_t maxThreads = 0;

    /* Create a new MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 0 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Set the task pool to an invalid state and cause all further scheduling to fail. */
    maxThreads = taskPool->maxThreads;
    taskPool->maxThreads = 0;

    /* Send a QoS 0 publish that fails to schedule. */
    publishInfo.pTopicName = "test/";
    publishInfo.topicNameLength = ( uint16_t ) strlen( publishInfo.pTopicName );
    publishInfo.pPayload = "";
    publishInfo.payloadLength = 0;

    status = IotMqtt_PublishAsync( pMqttConnection, &publishInfo, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_SCHEDULING_ERROR, status );

    /* Send a QoS 1 publish that fails to schedule. */
    publishInfo.qos = IOT_MQTT_QOS_1;
    status = IotMqtt_PublishAsync( pMqttConnection, &publishInfo, 0, NULL, &publishOperation );
    TEST_ASSERT_EQUAL( IOT_MQTT_SCHEDULING_ERROR, status );
    TEST_ASSERT_EQUAL( NULL, publishOperation );

    /* Restore the task pool to a valid state. */
    taskPool->maxThreads = maxThreads;

    /* Clean up. */
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior when a client-to-server PUBLISH retry fails to
 * schedule.
 */
TEST( MQTT_Unit_Platform, PublishRetryScheduleFailure )
{
    IotMqttConnection_t pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    _mqttOperation_t * pOperation = NULL;
    IotTaskPool_t taskPool = IOT_SYSTEM_TASKPOOL;
    uint32_t maxThreads = 0;

    /* Create a new MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 0 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Create a new PUBLISH with retry operation. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_CreateOperation( pMqttConnection,
                                                                   IOT_MQTT_FLAG_WAITABLE,
                                                                   NULL,
                                                                   &pOperation ) );
    TEST_ASSERT_NOT_NULL( pOperation );
    pOperation->u.operation.type = IOT_MQTT_PUBLISH_TO_SERVER;
    pOperation->u.operation.periodic.retry.limit = 3;
    pOperation->u.operation.periodic.retry.nextPeriodMs = TIMEOUT_MS;
    pOperation->u.operation.pMqttPacket = IotMqtt_MallocMessage( PACKET_LENGTH );
    pOperation->u.operation.packetSize = PACKET_LENGTH;

    /* Set the task pool to an invalid state and cause all further scheduling to fail. */
    maxThreads = taskPool->maxThreads;
    taskPool->maxThreads = 0;

    /* Send the MQTT PUBLISH. Retry will fail to schedule. */
    _IotMqtt_ProcessSend( IOT_SYSTEM_TASKPOOL, pOperation->job, pOperation );
    TEST_ASSERT_EQUAL( IOT_MQTT_SCHEDULING_ERROR, pOperation->u.operation.status );
    TEST_ASSERT_EQUAL_UINT32( 1, IotSemaphore_GetCount( &( pOperation->u.operation.notify.waitSemaphore ) ) );
    TEST_ASSERT_EQUAL_UINT32( 1, pOperation->u.operation.periodic.retry.count );

    /* Restore the task pool to a valid state. */
    taskPool->maxThreads = maxThreads;

    /* Clean up. */
    TEST_ASSERT_EQUAL_INT( true, _IotMqtt_DecrementOperationReferences( pOperation, false ) );
    _IotMqtt_DestroyOperation( pOperation );
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of the client-to-server PUBACK when scheduling and
 * serializing fail.
 */
TEST( MQTT_Unit_Platform, PubackScheduleSerializeFailure )
{
    IotMqttConnection_t pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    IotMqttSerializer_t serializer = IOT_MQTT_SERIALIZER_INITIALIZER;
    IotTaskPool_t taskPool = IOT_SYSTEM_TASKPOOL;
    uint32_t maxThreads = 0;

    /* Create a new MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 0 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Set the task pool to an invalid state and cause all further scheduling to fail. */
    maxThreads = taskPool->maxThreads;
    taskPool->maxThreads = 0;

    /* Call the function to send a PUBACK with scheduling failure. The failed PUBACK
     * should be cleaned up and not create memory leaks. */
    IotTestMqtt_sendPuback( pMqttConnection, 1 );

    /* Restore the task pool to a valid state. */
    taskPool->maxThreads = maxThreads;

    /* Call the function to send PUBACK with serializer failure. The failed PUBACK
     * should be cleaned up and not create memory leaks. */
    serializer.serialize.puback = _serializePuback;
    pMqttConnection->pSerializer = &serializer;
    IotTestMqtt_sendPuback( pMqttConnection, 1 );

    /* Clean up. */
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_subscribeasync and
 * @ref mqtt_function_unsubscribeasync when scheduling fails.
 */
TEST( MQTT_Unit_Platform, SubscriptionScheduleFailure )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnection_t pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotTaskPool_t taskPool = IOT_SYSTEM_TASKPOOL;
    IotMqttOperation_t subscriptionOperation = IOT_MQTT_OPERATION_INITIALIZER;
    uint32_t maxThreads = 0;

    /* Set subscription parameters. */
    subscription.pTopicFilter = "test/";
    subscription.topicFilterLength = ( uint16_t ) strlen( subscription.pTopicFilter );
    subscription.callback.function = SUBSCRIPTION_CALLBACK_FUNCTION;

    /* Create a new MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 0 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Set the task pool to an invalid state and cause all further scheduling to fail. */
    maxThreads = taskPool->maxThreads;
    taskPool->maxThreads = 0;

    /* Send a SUBSCRIBE that fails to schedule. */
    status = IotMqtt_SubscribeAsync( pMqttConnection, &subscription, 1, 0, NULL, &subscriptionOperation );
    TEST_ASSERT_EQUAL( status, IOT_MQTT_SCHEDULING_ERROR );

    /* Send an UNSUBSCRIBE that fails to schedule. */
    status = IotMqtt_UnsubscribeAsync( pMqttConnection, &subscription, 1, 0, NULL, &subscriptionOperation );
    TEST_ASSERT_EQUAL( status, IOT_MQTT_SCHEDULING_ERROR );

    /* Restore the task pool to a valid state. */
    taskPool->maxThreads = maxThreads;

    /* Clean up. */
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of #_IotMqtt_Notify when scheduling fails.
 */
TEST( MQTT_Unit_Platform, NotifyScheduleFailure )
{
    IotMqttConnection_t pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    _mqttOperation_t * pOperation = NULL;
    IotTaskPool_t taskPool = IOT_SYSTEM_TASKPOOL;
    uint32_t maxThreads = 0;

    /* Create a new MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( false, &_networkInfo, 0 );
    TEST_ASSERT_NOT_NULL( pMqttConnection );

    /* Create a new MQTT operation. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_CreateOperation( pMqttConnection, 0, NULL, &pOperation ) );
    TEST_ASSERT_NOT_NULL( pOperation );
    pOperation->u.operation.notify.callback.function = SUBSCRIPTION_CALLBACK_FUNCTION;

    /* Set the task pool to an invalid state and cause all further scheduling to fail. */
    maxThreads = taskPool->maxThreads;
    taskPool->maxThreads = 0;

    _IotMqtt_Notify( pOperation );

    /* Restore the task pool to a valid state. */
    taskPool->maxThreads = maxThreads;

    /* Clean up. */
    IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that MQTT can work in a single thread without the task pool.
 */
TEST( MQTT_Unit_Platform, SingleThreaded )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotTaskPoolInfo_t taskPoolInfo = IOT_TASKPOOL_INFO_INITIALIZER_SMALL;

    /* Shut down the system task pool to test if MQTT works without it. */
    IotTaskPool_Destroy( IOT_SYSTEM_TASKPOOL );

    /* Set the members of the subscription. */
    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK_FUNCTION;

    /* Set the members of the publish info. */
    publishInfo.pTopicName = TEST_TOPIC_NAME;
    publishInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;
    publishInfo.pPayload = "test";
    publishInfo.payloadLength = 4;
    publishInfo.qos = IOT_MQTT_QOS_1;

    if( TEST_PROTECT() )
    {
        /* Set up a mocked MQTT connection. */
        TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &mqttConnection ) );

        /* Add a subscription. */
        status = IotMqtt_SubscribeSync( mqttConnection, &subscription, 1, 0, DUP_CHECK_TIMEOUT );
        TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

        /* Transmit a message with no retry. */
        status = IotMqtt_PublishSync( mqttConnection, &publishInfo, 0, DUP_CHECK_TIMEOUT );
        TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

        /* Remove the subscription. */
        status = IotMqtt_UnsubscribeSync( mqttConnection, &subscription, 1, 0, DUP_CHECK_TIMEOUT );
        TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

        /* Re-initialize the system task pool. The task pool must be available to
         * send messages with a retry. */
        TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS, IotTaskPool_CreateSystemTaskPool( &taskPoolInfo ) );

        /* Transmit a message with a retry. */
        publishInfo.retryLimit = DUP_CHECK_RETRY_LIMIT;
        publishInfo.retryMs = DUP_CHECK_RETRY_MS;
        status = IotMqtt_PublishSync( mqttConnection, &publishInfo, 0, DUP_CHECK_TIMEOUT );
        TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

        IotTest_MqttMockCleanup();
    }
    else
    {
        /* Re-initialize the system task pool for test tear down. */
        TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS, IotTaskPool_CreateSystemTaskPool( &taskPoolInfo ) );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that subscriptions are properly reference counted.
 */
TEST( MQTT_Unit_Platform, SubscriptionReferences )
{
    int32_t i = 0;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    _mqttOperation_t * pIncomingPublish[ 3 ] = { NULL };
    _mqttSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink;
    IotSemaphore_t waitSem;
    _mqttConnection_t * pMqttConnection = NULL;

    /* Create an MQTT connection. */
    pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                        &_networkInfo,
                                                        0 );

    /* Adjustment to reference count based on keep-alive status. */
    const int32_t keepAliveReference = 1 + ( ( pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0 ) ? 1 : 0 );

    #if ( IOT_STATIC_MEMORY_ONLY == 1 ) && ( IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS < 3 )
    #error "IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS must be at least 3 for SubscriptionReferences test."
    #endif

    /* The MQTT task pool must support at least 3 threads for this test to run successfully. */
    TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS, IotTaskPool_SetMaxThreads( IOT_SYSTEM_TASKPOOL, 4 ) );

    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &waitSem, 0, 3 ) );

    /* Set the subscription info. */
    subscription.pTopicFilter = "/test";
    subscription.topicFilterLength = 5;
    subscription.callback.function = _blockingCallback;
    subscription.callback.pCallbackContext = &waitSem;

    /* Add the subscriptions. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_AddSubscriptions( pMqttConnection,
                                                                    1,
                                                                    &subscription,
                                                                    1 ) );

    /* Get the pointer to the subscription in the MQTT connection. */
    pSubscriptionLink = IotListDouble_PeekHead( &( pMqttConnection->subscriptionList ) );
    TEST_ASSERT_NOT_NULL( pSubscriptionLink );
    pSubscription = IotLink_Container( _mqttSubscription_t, pSubscriptionLink, link );
    TEST_ASSERT_NOT_NULL( pSubscription );

    /* Create 3 incoming PUBLISH messages that match the subscription. */
    for( i = 0; i < 3; i++ )
    {
        pIncomingPublish[ i ] = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );
        TEST_ASSERT_NOT_NULL( pIncomingPublish );

        ( void ) memset( pIncomingPublish[ i ], 0x00, sizeof( _mqttOperation_t ) );
        pIncomingPublish[ i ]->incomingPublish = true;
        pIncomingPublish[ i ]->pMqttConnection = pMqttConnection;
        pIncomingPublish[ i ]->u.publish.publishInfo.pTopicName = "/test";
        pIncomingPublish[ i ]->u.publish.publishInfo.topicNameLength = 5;
        pIncomingPublish[ i ]->u.publish.publishInfo.pPayload = "";
        pIncomingPublish[ i ]->u.publish.pReceivedData = IotMqtt_MallocMessage( 1 );

        IotListDouble_InsertHead( &( pMqttConnection->pendingProcessing ),
                                  &( pIncomingPublish[ i ]->link ) );
    }

    if( TEST_PROTECT() )
    {
        /* Schedule 3 callback invocations for the incoming PUBLISH. */
        for( i = 0; i < 3; i++ )
        {
            TEST_ASSERT_EQUAL_INT( true, _IotMqtt_IncrementConnectionReferences( pMqttConnection ) );
            TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_ScheduleOperation( pIncomingPublish[ i ],
                                                                             _IotMqtt_ProcessIncomingPublish,
                                                                             0 ) );
        }

        /* Wait for the connection reference count to reach 3 (adjusted for possible keep-alive). */
        TEST_ASSERT_EQUAL_INT( true, _waitForCount( &( pMqttConnection->referencesMutex ),
                                                    &( pMqttConnection->references ),
                                                    3 + keepAliveReference ) );

        /* Check that the subscription also has a reference count of 3. */
        TEST_ASSERT_EQUAL_INT32( true, _waitForCount( &( pMqttConnection->subscriptionMutex ),
                                                      &( pSubscription->references ),
                                                      3 ) );

        /* Post to the wait semaphore, which unblocks one subscription callback. */
        IotSemaphore_Post( &waitSem );

        /* Wait for the connection reference count to decrease to 2 (adjusted for
         * possible keep-alive). Check that the subscription reference count also
         * decreases to 2. */
        TEST_ASSERT_EQUAL_INT( true, _waitForCount( &( pMqttConnection->referencesMutex ),
                                                    &( pMqttConnection->references ),
                                                    2 + keepAliveReference ) );
        TEST_ASSERT_EQUAL_INT32( true, _waitForCount( &( pMqttConnection->subscriptionMutex ),
                                                      &( pSubscription->references ),
                                                      2 ) );

        /* Shut down the MQTT connection. */
        IotMqtt_Disconnect( pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );

        /* Post twice to the wait semaphore, which unblocks the remaining blocking
         * callbacks. */
        IotSemaphore_Post( &waitSem );
        IotSemaphore_Post( &waitSem );

        /* Wait for the callbacks to exit. */
        while( IotSemaphore_GetCount( &waitSem ) > 0 )
        {
            IotClock_SleepMs( 100 );
        }
    }

    IotSemaphore_Destroy( &waitSem );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test the behavior when the subscription list exceeds the size of an MQTT
 * packet. Requires a large amount of memory not available on smaller systems.
 */
TEST( MQTT_Unit_Platform, SubscriptionListTooLarge )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    size_t subscriptionCount = MQTT_MAX_REMAINING_LENGTH / UINT16_MAX + 1, i = 0;
    size_t remainingLength = 0, packetSize = 0;
    IotMqttSubscription_t * pSubscriptionList = IotTest_Malloc( subscriptionCount * sizeof( IotMqttSubscription_t ) );

    TEST_ASSERT_NOT_NULL( pSubscriptionList );
    ( void ) memset( pSubscriptionList, 0x00, subscriptionCount * sizeof( IotMqttSubscription_t ) );

    for( i = 0; i < subscriptionCount; i++ )
    {
        pSubscriptionList[ i ].topicFilterLength = UINT16_MAX;
    }

    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                pSubscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that API functions can be invoked from a callback for a completed
 * subscription operation.
 */
TEST( MQTT_System_Platform, SubscribeCompleteReentrancy )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttCallbackInfo_t callbackInfo = IOT_MQTT_CALLBACK_INFO_INITIALIZER;

    /* Two semaphores are needed for this test: one for incoming PUBLISH and one
     * for test completion. */
    IotSemaphore_t pWaitSemaphores[ 2 ];

    /* The topic to use for this test. */
    GENERATE_TOPIC_WITH_SUFFIX( pTopic, "/Reentrancy" );

    /* Create the semaphores. */
    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &( pWaitSemaphores[ 0 ] ), 0, 1 ) );

    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &( pWaitSemaphores[ 1 ] ), 0, 1 ) );

        if( TEST_PROTECT() )
        {
            connectInfo.awsIotMqttMode = AWS_IOT_MQTT_SERVER;
            connectInfo.pClientIdentifier = _pClientIdentifier;
            connectInfo.clientIdentifierLength = ( uint16_t ) strlen( _pClientIdentifier );

            if( TEST_PROTECT() )
            {
                /* Establish the MQTT connection. */
                status = _mqttConnect( &_reentrantNetworkInfo,
                                       &connectInfo,
                                       IOT_TEST_MQTT_TIMEOUT_MS,
                                       &_mqttConnection );
                TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, status );

                /* Subscribe with a completion callback. */
                subscription.qos = IOT_MQTT_QOS_1;
                subscription.pTopicFilter = pTopic;
                subscription.topicFilterLength = ( uint16_t ) strlen( subscription.pTopicFilter );
                subscription.callback.function = _publishReceived;
                subscription.callback.pCallbackContext = &( pWaitSemaphores[ 0 ] );

                callbackInfo.function = _reentrantCallback;
                callbackInfo.pCallbackContext = pWaitSemaphores;

                status = IotMqtt_SubscribeAsync( _mqttConnection,
                                                 &subscription,
                                                 1,
                                                 0,
                                                 &callbackInfo,
                                                 NULL );
                TEST_ASSERT_EQUAL( IOT_MQTT_STATUS_PENDING, status );

                /* Wait for the reentrant callback to complete. */
                if( IotSemaphore_TimedWait( &( pWaitSemaphores[ 1 ] ),
                                            IOT_TEST_MQTT_TIMEOUT_MS ) == false )
                {
                    TEST_FAIL_MESSAGE( "Timed out waiting for reentrant callback." );
                }
            }
        }

        IotSemaphore_Destroy( &( pWaitSemaphores[ 1 ] ) );
    }

    IotSemaphore_Destroy( &( pWaitSemaphores[ 0 ] ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that API functions can be invoked from a callback for an incoming
 * PUBLISH.
 */
TEST( MQTT_System_Platform, IncomingPublishReentrancy )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttSubscription_t pSubscription[ 2 ] = { IOT_MQTT_SUBSCRIPTION_INITIALIZER };
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    /* Two semaphores are needed for this test: one for incoming PUBLISH and one
     * for test completion. */
    IotSemaphore_t pWaitSemaphores[ 2 ];

    /* The topics to use for this test. */
    GENERATE_TOPIC_WITH_SUFFIX( pTopic1, "/IncomingPublishReentrancy" );
    GENERATE_TOPIC_WITH_SUFFIX( pTopic2, "/Reentrancy" );

    /* Create the semaphores. */
    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &( pWaitSemaphores[ 0 ] ), 0, 1 ) );

    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &( pWaitSemaphores[ 1 ] ), 0, 1 ) );

        if( TEST_PROTECT() )
        {
            connectInfo.awsIotMqttMode = AWS_IOT_MQTT_SERVER;
            connectInfo.pClientIdentifier = _pClientIdentifier;
            connectInfo.clientIdentifierLength = ( uint16_t ) strlen( _pClientIdentifier );

            if( TEST_PROTECT() )
            {
                /* Establish the MQTT connection. */
                status = _mqttConnect( &_reentrantNetworkInfo,
                                       &connectInfo,
                                       IOT_TEST_MQTT_TIMEOUT_MS,
                                       &_mqttConnection );
                TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, status );

                /* Subscribe with to the test topics. */
                pSubscription[ 0 ].qos = IOT_MQTT_QOS_1;
                pSubscription[ 0 ].pTopicFilter = pTopic1;
                pSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( pSubscription[ 0 ].pTopicFilter );
                pSubscription[ 0 ].callback.function = _reentrantCallback;
                pSubscription[ 0 ].callback.pCallbackContext = pWaitSemaphores;

                pSubscription[ 1 ].qos = IOT_MQTT_QOS_1;
                pSubscription[ 1 ].pTopicFilter = pTopic2;
                pSubscription[ 1 ].topicFilterLength = ( uint16_t ) strlen( pSubscription[ 1 ].pTopicFilter );
                pSubscription[ 1 ].callback.function = _publishReceived;
                pSubscription[ 1 ].callback.pCallbackContext = &( pWaitSemaphores[ 0 ] );

                status = IotMqtt_SubscribeSync( _mqttConnection,
                                                pSubscription,
                                                2,
                                                0,
                                                IOT_TEST_MQTT_TIMEOUT_MS );
                TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, status );

                /* Publish a message to the test topic. */
                publishInfo.qos = IOT_MQTT_QOS_1;
                publishInfo.pTopicName = pTopic1;
                publishInfo.topicNameLength = ( uint16_t ) strlen( publishInfo.pTopicName );
                publishInfo.pPayload = _pSamplePayload;
                publishInfo.payloadLength = _samplePayloadLength;
                publishInfo.retryLimit = IOT_TEST_MQTT_PUBLISH_RETRY_COUNT;
                publishInfo.retryMs = IOT_TEST_MQTT_TIMEOUT_MS;

                status = IotMqtt_PublishSync( _mqttConnection,
                                              &publishInfo,
                                              0,
                                              IOT_TEST_MQTT_TIMEOUT_MS );
                TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, status );

                /* Wait for the reentrant callback to complete. */
                if( IotSemaphore_TimedWait( &( pWaitSemaphores[ 1 ] ),
                                            IOT_TEST_MQTT_TIMEOUT_MS ) == false )
                {
                    TEST_FAIL_MESSAGE( "Timed out waiting for reentrant callback." );
                }
            }
        }

        IotSemaphore_Destroy( &( pWaitSemaphores[ 1 ] ) );
    }

    IotSemaphore_Destroy( &( pWaitSemaphores[ 0 ] ) );
}

/*-----------------------------------------------------------*/
