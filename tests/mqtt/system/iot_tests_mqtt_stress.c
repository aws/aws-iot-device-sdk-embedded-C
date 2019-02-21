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
 * @file iot_tests_mqtt_stress.c
 * @brief Stress tests for the MQTT library.
 *
 * The tests in this file run far longer than other tests, and may easily fail
 * due to poor network conditions. For best results, these tests should be run
 * on a stable local network (not the Internet).
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <string.h>

/* POSIX includes. */
#include <time.h>

/* MQTT include. */
#include "iot_mqtt.h"

/* POSIX includes. */
#ifdef POSIX_PTHREAD_HEADER
    #include POSIX_PTHREAD_HEADER
#else
    #include <pthread.h>
#endif
#ifdef POSIX_UNISTD_HEADER
    #include POSIX_UNISTD_HEADER
#else
    #include <unistd.h>
#endif

/* Platform layer include. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* Test framework includes. */
#include "unity_fixture.h"

/* The tests in this file run for a long time, so set up logging to track their
 * progress. */
#define _LIBRARY_LOG_LEVEL    IOT_LOG_INFO
#define _LIBRARY_LOG_NAME     ( "MQTT_STRESS" )
#include "iot_logging_setup.h"

/**
 * @brief Determine which MQTT server mode to test (AWS IoT or Mosquitto).
 */
#if !defined( IOT_TEST_MQTT_MOSQUITTO ) || IOT_TEST_MQTT_MOSQUITTO == 0
    #define _AWS_IOT_MQTT_SERVER    true
#else
    #define _AWS_IOT_MQTT_SERVER    false

/* Redefine the connect info initializer if not using an AWS IoT MQTT server. */
    #undef IOT_MQTT_CONNECT_INFO_INITIALIZER
    #define IOT_MQTT_CONNECT_INFO_INITIALIZER    { 0 }
#endif

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values of test configuration constants.
 */
#ifndef IOT_TEST_MQTT_TIMEOUT_MS
    #define IOT_TEST_MQTT_TIMEOUT_MS      ( 5000 )
#endif
#ifndef IOT_TEST_MQTT_TOPIC_PREFIX
    #define IOT_TEST_MQTT_TOPIC_PREFIX    "iotmqtttest"
#endif
#ifndef IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S
    #if IOT_TEST_MQTT_MOSQUITTO == 1
        #define IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S    ( 5 )
    #else
        #define IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S    ( 30 )
    #endif
#endif
#ifndef IOT_TEST_MQTT_RETRY_MS
    #define IOT_TEST_MQTT_RETRY_MS       ( 350 )
#endif
#ifndef IOT_TEST_MQTT_RETRY_LIMIT
    #define IOT_TEST_MQTT_RETRY_LIMIT    ( 32 )
#endif
#ifndef IOT_TEST_MQTT_DECONGEST_S
    #define IOT_TEST_MQTT_DECONGEST_S    ( 30 )
#endif
#ifndef IOT_TEST_MQTT_THREADS
    #define IOT_TEST_MQTT_THREADS        ( 16 )
#endif
#ifndef IOT_TEST_MQTT_PUBLISHES_PER_THREAD
    #ifdef IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS
        #define IOT_TEST_MQTT_PUBLISHES_PER_THREAD    ( IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS )
    #else
        #define IOT_TEST_MQTT_PUBLISHES_PER_THREAD    ( 100 )
    #endif
#endif
/** @endcond */

/**
 * @brief Number of test topic names.
 */
#define _TEST_TOPIC_NAME_COUNT    ( 8 )

/**
 * @brief The maximum number of PUBLISH messages that will be received by a
 * single test.
 */
#define _MAX_RECEIVED_PUBLISH     ( IOT_TEST_MQTT_THREADS * IOT_TEST_MQTT_PUBLISHES_PER_THREAD )

/**
 * @brief The maximum length of an MQTT client identifier.
 */
#ifdef IOT_TEST_MQTT_CLIENT_IDENTIFIER
    #define _CLIENT_IDENTIFIER_MAX_LENGTH    ( sizeof( IOT_TEST_MQTT_CLIENT_IDENTIFIER ) )
#else
    #define _CLIENT_IDENTIFIER_MAX_LENGTH    ( 24 )
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Parameter 1 of #_publishThread.
 */
typedef struct _publishParams
{
    int threadNumber;      /**< @brief ID number of this publish thread. */
    long publishPeriodNs;  /**< @brief How long to wait (in nanoseconds) between each publish. */
    unsigned publishLimit; /**< @brief How many publishes this thread will send. */
    IotMqttError_t status; /**< @brief Final status of this publish thread. */
} _publishParams_t;

/*-----------------------------------------------------------*/

/* Network functions used by the tests, declared and implemented in one of
 * the test network function files. */
extern bool IotTest_NetworkSetup( void );
extern void IotTest_NetworkCleanup( void );

/* Extern declarations of default serializer functions. The internal MQTT header cannot
 * be included by this file. */
extern IotMqttError_t _IotMqtt_SerializePingreq( uint8_t ** pPingreqPacket,
                                                 size_t * pPacketSize );
extern void _IotMqtt_FreePacket( uint8_t * pPacket );

/* Network variables used by the tests, declared in one of the test network
 * function files. */
extern IotMqttNetIf_t _IotTestNetworkInterface;
extern IotMqttConnection_t _IotTestMqttConnection;

/*-----------------------------------------------------------*/

/**
 * @brief Filler text to publish.
 */
static const char _pSamplePayload[] =
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
 * @brief Topic names used in the stress tests.
 *
 * For convenience, all topic names are the same length.
 */
static const char * const _pTopicNames[ _TEST_TOPIC_NAME_COUNT ] =
{
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/0",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/1",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/2",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/3",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/4",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/5",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/6",
    IOT_TEST_MQTT_TOPIC_PREFIX "/stress/7"
};

/**
 * @brief Length of topic names used in the stress tests.
 *
 * For convenience, all topic names are the same length.
 */
static const uint16_t _topicNameLength = ( uint16_t ) sizeof( IOT_TEST_MQTT_TOPIC_PREFIX "/stress/0" ) - 1;

/**
 * @brief Counts how many subscriptions were received for each test.
 *
 * Used in conjunction with #_publishReceived.
 */
static IotSemaphore_t receivedPublishCounter;

/**
 * @brief Buffer holding the client identifier used for the tests.
 */
static char _pClientIdentifier[ _CLIENT_IDENTIFIER_MAX_LENGTH ] = { 0 };

/**
 * @brief Tracks whether the PINGREQ serializer override was called.
 */
static bool _pingreqOverrideCalled = false;

/*-----------------------------------------------------------*/

/**
 * @brief Serializer override for PINGREQ.
 */
static IotMqttError_t _serializePingreq( uint8_t ** pPingreqPacket,
                                         size_t * pPacketSize )
{
    _pingreqOverrideCalled = true;

    return _IotMqtt_SerializePingreq( pPingreqPacket, pPacketSize );
}

/*-----------------------------------------------------------*/

/**
 * @brief Checks that #_IotTestMqttConnection is still usable by sending a PUBLISH.
 *
 * @return The result of the PUBLISH.
 */
static IotMqttError_t _checkConnection( void )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttReference_t publishRef = IOT_MQTT_REFERENCE_INITIALIZER;

    /* Set the publish info. */
    publishInfo.qos = IOT_MQTT_QOS_1;
    publishInfo.pTopicName = _pTopicNames[ 0 ];
    publishInfo.topicNameLength = _topicNameLength;
    publishInfo.pPayload = _pSamplePayload;
    publishInfo.payloadLength = _samplePayloadLength;
    publishInfo.retryMs = IOT_TEST_MQTT_RETRY_MS;
    publishInfo.retryLimit = IOT_TEST_MQTT_RETRY_LIMIT;

    /* Send a PUBLISH. */
    status = IotMqtt_Publish( _IotTestMqttConnection,
                              &publishInfo,
                              IOT_MQTT_FLAG_WAITABLE,
                              NULL,
                              &publishRef );

    if( status != IOT_MQTT_STATUS_PENDING )
    {
        return status;
    }

    /* Return the result of the PUBLISH. */
    return IotMqtt_Wait( publishRef,
                         IOT_TEST_MQTT_TIMEOUT_MS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Subscription callback function.
 */
static void _publishReceived( void * pArgument,
                              IotMqttCallbackParam_t * pPublish )
{
    ( void ) pArgument;

    /* Increment the received PUBLISH counter if the received message matches
     * what was published. */
    if( ( pPublish->message.info.payloadLength == _samplePayloadLength ) &&
        ( strncmp( _pSamplePayload, pPublish->message.info.pPayload, _samplePayloadLength ) == 0 ) &&
        ( pPublish->message.info.topicNameLength == _topicNameLength ) &&
        ( pPublish->message.info.qos == IOT_MQTT_QOS_1 ) )
    {
        IotSemaphore_Post( &receivedPublishCounter );
    }
    else
    {
        IotLogWarn( "Received an unknown message on subscription %.*s: %.*s",
                    pPublish->message.info.topicNameLength, pPublish->message.info.pTopicName,
                    pPublish->message.info.payloadLength, pPublish->message.info.pPayload );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback function that blocks for a long time.
 */
static void _blockingCallback( void * pArgument,
                               IotMqttCallbackParam_t * param )
{
    IotSemaphore_t * pWaitSem = ( IotSemaphore_t * ) pArgument;
    const unsigned blockTime = 5 * IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S;

    ( void ) param;

    IotLogInfo( "Callback blocking for %u seconds.", blockTime );
    sleep( blockTime );
    IotSemaphore_Post( pWaitSem );
}

/*-----------------------------------------------------------*/

/**
 * @brief Periodically sends PUBLISH messages.
 *
 * @param[in] pArgument Pointer to a #_publishParams_t.
 */
static void * _publishThread( void * pArgument )
{
    unsigned i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _publishParams_t * pParams = ( _publishParams_t * ) pArgument;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    const struct timespec sleepTime =
    {
        .tv_sec  = 0,
        .tv_nsec = pParams->publishPeriodNs
    };

    /* Set the publish info. */
    publishInfo.qos = IOT_MQTT_QOS_1;
    publishInfo.pPayload = _pSamplePayload;
    publishInfo.payloadLength = _samplePayloadLength;
    publishInfo.topicNameLength = _topicNameLength;
    publishInfo.retryMs = IOT_TEST_MQTT_RETRY_MS;
    publishInfo.retryLimit = IOT_TEST_MQTT_RETRY_LIMIT;

    for( i = 0; i < pParams->publishLimit; )
    {
        /* Choose a topic name. */
        publishInfo.pTopicName = _pTopicNames[ i % _TEST_TOPIC_NAME_COUNT ];

        /* PUBLISH the message. */
        status = IotMqtt_Publish( _IotTestMqttConnection,
                                  &publishInfo,
                                  0,
                                  NULL,
                                  NULL );

        /* The stress tests may exhaust all memory available to the MQTT library.
         * If no memory is available, wait some time for resources to be released. */
        if( status == IOT_MQTT_NO_MEMORY )
        {
            IotLogInfo( "Thread %d: no memory available on PUBLISH %d."
                        " Sleeping for %d seconds.",
                        pParams->threadNumber,
                        i,
                        IOT_TEST_MQTT_DECONGEST_S );
            sleep( IOT_TEST_MQTT_DECONGEST_S );
            continue;
        }
        /* If the PUBLISH failed, exit this thread. */
        else if( status != IOT_MQTT_STATUS_PENDING )
        {
            IotLogError( "Thread %d encountered error %d publishing message %d.",
                         status, i );
            break;
        }

        /* Only increment the loop counter if the PUBLISH succeeded. */
        i++;

        /* Occasionally print an update on how many PUBLISH messages this thread
         * has sent. */
        if( ( i % 25 == 0 ) ||
            ( i == pParams->publishLimit ) )
        {
            IotLogInfo( "Thread %d has published %d of %d messages.",
                        pParams->threadNumber, i, pParams->publishLimit );
        }

        /* Sleep until the next PUBLISH should be sent. */
        if( nanosleep( &sleepTime, NULL ) != 0 )
        {
            IotLogError( "Error in nanosleep." );
            status = IOT_MQTT_BAD_RESPONSE;
            break;
        }
    }

    /* Set the thread's last status. */
    pParams->status = status;

    return NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for MQTT stress tests.
 */
TEST_GROUP( MQTT_Stress );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for MQTT stress tests.
 */
TEST_SETUP( MQTT_Stress )
{
    int i = 0;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttSubscription_t pSubscriptions[ _TEST_TOPIC_NAME_COUNT ] = { IOT_MQTT_SUBSCRIPTION_INITIALIZER };
    const IotLogConfig_t logHideAll = { .hideLogLevel = true, .hideLibraryName = true, .hideTimestring = true };

    /* Clear the PINGREQ override flag. */
    _pingreqOverrideCalled = false;

    /* Empty log message to log a new line. */
    IotLog( IOT_LOG_INFO, &logHideAll, " " );

    /* Create the publish counter semaphore. */
    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &receivedPublishCounter,
                                                      0,
                                                      _MAX_RECEIVED_PUBLISH ) );

    /* Set the serializer overrides. */
    _IotTestNetworkInterface.serialize.pingreq = _serializePingreq;
    _IotTestNetworkInterface.freePacket = _IotMqtt_FreePacket;

    /* Set up the network stack. */
    if( IotTest_NetworkSetup() == false )
    {
        TEST_FAIL_MESSAGE( "Failed to set up network connection." );
    }

    /* Initialize the MQTT library. */
    if( IotMqtt_Init() != IOT_MQTT_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize MQTT library." );
    }

    /* Generate a new, unique client identifier based on the time if no client
     * identifier is defined. Otherwise, copy the provided client identifier. */
    #ifndef IOT_TEST_MQTT_CLIENT_IDENTIFIER
        ( void ) snprintf( _pClientIdentifier,
                           _CLIENT_IDENTIFIER_MAX_LENGTH,
                           "iot%llu",
                           ( long long unsigned int ) IotClock_GetTimeMs() );
    #else
        ( void ) strncpy( _pClientIdentifier,
                          IOT_TEST_MQTT_CLIENT_IDENTIFIER,
                          _CLIENT_IDENTIFIER_MAX_LENGTH );
    #endif

    /* Set the members of the connect info. */
    connectInfo.cleanSession = true;
    connectInfo.keepAliveSeconds = IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S;
    connectInfo.pClientIdentifier = _pClientIdentifier;
    connectInfo.clientIdentifierLength = ( uint16_t ) strlen( _pClientIdentifier );

    /* Set the members of the subscriptions */
    for( i = 0; i < _TEST_TOPIC_NAME_COUNT; i++ )
    {
        pSubscriptions[ i ].pTopicFilter = _pTopicNames[ i ];
        pSubscriptions[ i ].topicFilterLength = _topicNameLength;
        pSubscriptions[ i ].qos = IOT_MQTT_QOS_1;
        pSubscriptions[ i ].callback.function = _publishReceived;
    }

    /* Establish the MQTT connection. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS,
                       IotMqtt_Connect( &_IotTestMqttConnection,
                                        &_IotTestNetworkInterface,
                                        &connectInfo,
                                        IOT_TEST_MQTT_TIMEOUT_MS ) );

    /* Subscribe to the test topic filters. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS,
                       IotMqtt_TimedSubscribe( _IotTestMqttConnection,
                                               pSubscriptions,
                                               _TEST_TOPIC_NAME_COUNT,
                                               0,
                                               IOT_TEST_MQTT_TIMEOUT_MS ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for MQTT stress tests.
 */
TEST_TEAR_DOWN( MQTT_Stress )
{
    /* Destroy the PUBLISH counter semaphore. */
    IotSemaphore_Destroy( &receivedPublishCounter );

    /* Disconnect the MQTT connection. Unsubscribe is not called; the subscriptions
     * should be cleaned up by Disconnect. */
    if( _IotTestMqttConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotMqtt_Disconnect( _IotTestMqttConnection, false );
    }

    /* Clean up the network stack. */
    IotTest_NetworkCleanup();

    /* Clean up the MQTT library. */
    IotMqtt_Cleanup();
    _IotTestMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for MQTT stress tests.
 */
TEST_GROUP_RUNNER( MQTT_Stress )
{
    RUN_TEST_CASE( MQTT_Stress, KeepAlive );
    RUN_TEST_CASE( MQTT_Stress, BlockingCallback );
    RUN_TEST_CASE( MQTT_Stress, ClientClosesConnection );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that keep-alive keeps an idle connection open.
 */
TEST( MQTT_Stress, KeepAlive )
{
    const unsigned sleepTime = 5 * IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S;

    /* Send no MQTT packets for a long time. The keep-alive must be used to keep
     * the connection open. */
    IotLogInfo( "KeepAlive test sleeping for %u seconds.", sleepTime );
    sleep( sleepTime );

    /* Send a PUBLISH to verify that the connection is still usable. */
    IotLogInfo( "KeepAlive test checking MQTT connection." );
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _checkConnection() );

    /* Check that the PINGREQ override was used. */
    TEST_ASSERT_EQUAL( true, _pingreqOverrideCalled );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that the MQTT connection is not closed if a user callback blocks.
 */
TEST( MQTT_Stress, BlockingCallback )
{
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttCallbackInfo_t callbackInfo = IOT_MQTT_CALLBACK_INFO_INITIALIZER;
    IotSemaphore_t waitSem;

    callbackInfo.function = _blockingCallback;
    callbackInfo.param1 = &waitSem;

    publishInfo.qos = IOT_MQTT_QOS_1;
    publishInfo.pTopicName = _pTopicNames[ 0 ];
    publishInfo.topicNameLength = _topicNameLength;
    publishInfo.pPayload = _pSamplePayload;
    publishInfo.payloadLength = _samplePayloadLength;
    publishInfo.retryMs = IOT_TEST_MQTT_RETRY_MS;
    publishInfo.retryLimit = IOT_TEST_MQTT_RETRY_LIMIT;

    /* Create the wait semaphore. */
    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &waitSem, 0, 1 ) );

    if( TEST_PROTECT() )
    {
        /* Call a function that will invoke the blocking callback. */
        TEST_ASSERT_EQUAL( IOT_MQTT_STATUS_PENDING,
                           IotMqtt_Publish( _IotTestMqttConnection,
                                            &publishInfo,
                                            0,
                                            &callbackInfo,
                                            NULL ) );

        /* Wait for the callback to return, then check that the connection is
         * still usable. */
        IotSemaphore_Wait( &waitSem );
        IotLogInfo( "BlockingCallback test checking MQTT connection." );
        TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _checkConnection() );
    }

    IotSemaphore_Destroy( &waitSem );

    /* Check that the PINGREQ override was used. */
    TEST_ASSERT_EQUAL( true, _pingreqOverrideCalled );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test the behavior of the MQTT library when the network connection is
 * closed by the client.
 */
TEST( MQTT_Stress, ClientClosesConnection )
{
    int i = 0, threadsCreated = 0, threadsJoined = 0;
    pthread_t publishThreads[ IOT_TEST_MQTT_THREADS ] = { 0 };
    _publishParams_t publishThreadParams[ IOT_TEST_MQTT_THREADS ] = { 0 };

    /* Set the parameters for each thread. */
    for( i = 0; i < IOT_TEST_MQTT_THREADS; i++ )
    {
        publishThreadParams[ i ].threadNumber = i;
        publishThreadParams[ i ].publishPeriodNs = 500000000;
        publishThreadParams[ i ].publishLimit = IOT_TEST_MQTT_PUBLISHES_PER_THREAD;
    }

    IotLogInfo( "ClientClosesConnection test creating threads." );

    /* Spawn the threads for the test. */
    for( i = 0; i < IOT_TEST_MQTT_THREADS; i++ )
    {
        if( pthread_create( &( publishThreads[ i ] ),
                            NULL,
                            _publishThread,
                            &( publishThreadParams[ i ] ) ) != 0 )
        {
            break;
        }
    }

    /* Record how many threads were created. */
    threadsCreated = i;

    /* Wait for all created threads to finish. */
    for( i = 0; i < threadsCreated; i++ )
    {
        if( pthread_join( publishThreads[ i ], NULL ) == 0 )
        {
            threadsJoined++;
        }
    }
}

/*-----------------------------------------------------------*/
