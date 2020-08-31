/*
 * IoT MQTT V2.1.0
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
 * @file iot_tests_mqtt_api.c
 * @brief Tests for the user-facing API functions (declared in iot_mqtt.h).
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* Test framework includes. */
#include "unity_fixture.h"

/* MQTT test access include. */
#include "iot_test_access_mqtt.h"

/* MQTT serializer API include */
#include "iot_mqtt_serialize.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

/* Atomics include. */
#include "iot_atomic.h"

/*-----------------------------------------------------------*/

/**
 * @brief Determine which MQTT server mode to test (AWS IoT or Mosquitto).
 */
#if !defined( IOT_TEST_MQTT_MOSQUITTO ) || IOT_TEST_MQTT_MOSQUITTO == 0
    #define AWS_IOT_MQTT_SERVER    true
#else
    #define AWS_IOT_MQTT_SERVER    false
#endif

/**
 * @brief Timeout to use for the tests. This can be short, but should allow time
 * for other threads to run.
 */
#define TIMEOUT_MS                  ( 400 )

/**
 * @brief A short keep-alive interval to use for the keep-alive tests. It may be
 * shorter than the minimum 1 second specified by the MQTT spec.
 */
#define SHORT_KEEP_ALIVE_MS         ( 100 )

/**
 * @brief The number of times the periodic keep-alive should run.
 */
#define KEEP_ALIVE_COUNT            ( 10 )

/*
 * Client identifier and length to use for the MQTT API tests.
 */
#define CLIENT_IDENTIFIER           ( "test" )                                           /**< @brief Client identifier. */
#define CLIENT_IDENTIFIER_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) ) /**< @brief Length of client identifier. */

/*
 * Will topic name and length to use for the MQTT API tests.
 */
#define TEST_TOPIC_NAME             ( "/test/topic" )                                  /**< @brief An arbitrary topic name. */
#define TEST_TOPIC_NAME_LENGTH      ( ( uint16_t ) ( sizeof( TEST_TOPIC_NAME ) - 1 ) ) /**< @brief Length of topic name. */

/**
 * @brief A non-NULL function pointer to use for subscription callback. This
 * "function" should cause a crash if actually called.
 */
#define SUBSCRIPTION_CALLBACK \
    ( ( void ( * )( void *,   \
                    IotMqttCallbackParam_t * ) ) 0x01 )

/**
 * @brief How many times #TEST_MQTT_Unit_API_DisconnectMallocFail_ will test
 * malloc failures.
 *
 * The DISCONNECT function provides no mechanism to wait on its successful
 * completion. Therefore, this function simply uses the value below as an estimate
 * for the maximum number of times DISCONNECT will use malloc.
 */
#define DISCONNECT_MALLOC_LIMIT    ( 20 )

/*
 * Constants that affect the behavior of #TEST_MQTT_Unit_API_PublishDuplicates.
 */
#define DUP_CHECK_RETRY_MS         ( 100 )  /**< @brief When to start sending duplicate packets. */
#define DUP_CHECK_RETRY_LIMIT      ( 3 )    /**< @brief How many duplicate packets to send. */
#define DUP_CHECK_TIMEOUT          ( 3000 ) /**< @brief Total time allowed to send all duplicate packets.
                                             * Duplicates are sent using an exponential backoff strategy. */
/** @brief The minimum amount of time the test can take. */
#define DUP_CHECK_MINIMUM_WAIT \
    ( DUP_CHECK_RETRY_MS +     \
      2 * DUP_CHECK_RETRY_MS + \
      4 * DUP_CHECK_RETRY_MS + \
      IOT_MQTT_RESPONSE_WAIT_MS )

/*-----------------------------------------------------------*/

/**
 * @brief Tracks whether #_publishSetDup has been called.
 */
static bool _publishSetDupCalled = false;

/**
 * @brief Counts how many time #_sendPingreq has been called.
 */
static uint32_t _pingreqSendCount = 0;

/**
 * @brief Counts how many times #_close has been called.
 */
static uint32_t _closeCount = 0;

/**
 * @brief Counts how many times #_disconnectCallback has been called.
 */
static uint32_t _disconnectCallbackCount = 0;

/**
 * @brief An MQTT connection to share among the tests.
 */
static _mqttConnection_t * _pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/**
 * @brief An #IotMqttNetworkInfo_t to share among the tests.
 */
static IotMqttNetworkInfo_t _networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief An #IotNetworkInterface_t to share among the tests.
 */
static IotNetworkInterface_t _networkInterface = { 0 };

/*-----------------------------------------------------------*/

/**
 * @brief A thread routine that simulates an incoming PINGRESP.
 */
static void _incomingPingresp( void * pArgument )
{
    /* Silence warnings about unused parameters. */
    ( void ) pArgument;

    /* This test will not work if the response wait time is too small. */
    #if IOT_MQTT_RESPONSE_WAIT_MS < ( 2 * SHORT_KEEP_ALIVE_MS + 100 )
    #error "IOT_MQTT_RESPONSE_WAIT_MS too small for keep-alive tests."
    #endif

    static int32_t invokeCount = 0;
    static uint64_t lastInvokeTime = 0;
    uint64_t currentTime = IotClock_GetTimeMs();

    /* Increment invoke count for this function. */
    invokeCount++;

    /* Sleep to simulate the network round-trip time. */
    IotClock_SleepMs( 2 * SHORT_KEEP_ALIVE_MS );

    /* Respond with a PINGRESP. */
    if( invokeCount <= KEEP_ALIVE_COUNT )
    {
        /* Log a status with Unity, as this test may take a while. */
        UnityPrint( "KeepAlivePeriodic " );
        UnityPrintNumber( ( UNITY_INT ) invokeCount );
        UnityPrint( " of " );
        UnityPrintNumber( ( UNITY_INT ) KEEP_ALIVE_COUNT );
        UnityPrint( " DONE at " );
        UnityPrintNumber( ( UNITY_INT ) IotClock_GetTimeMs() );
        UnityPrint( " ms" );

        if( invokeCount > 1 )
        {
            UnityPrint( " (+" );
            UnityPrintNumber( ( UNITY_INT ) ( currentTime - lastInvokeTime ) );
            UnityPrint( " ms)." );
        }
        else
        {
            UnityPrint( "." );
        }

        UNITY_PRINT_EOL();
        lastInvokeTime = currentTime;

        IotMqtt_ReceiveCallback( NULL,
                                 _pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief PUBLISH set DUP function override.
 */
static void _publishSetDup( uint8_t * pPublishPacket,
                            uint8_t * pPacketIdentifierHigh,
                            uint16_t * pNewPacketIdentifier )
{
    _publishSetDupCalled = true;

    _IotMqtt_PublishSetDup( pPublishPacket,
                            pPacketIdentifierHigh,
                            pNewPacketIdentifier );
}

/*-----------------------------------------------------------*/

/**
 * @brief A send function that always "succeeds". May report that it was invoked
 * through a semaphore.
 */
static size_t _sendSuccess( IotNetworkConnection_t pSendContext,
                            const uint8_t * pMessage,
                            size_t messageLength )
{
    IotSemaphore_t * pWaitSem = ( IotSemaphore_t * ) pSendContext;

    /* Silence warnings about unused parameters. */
    ( void ) pMessage;

    /* Post to the wait semaphore if given. */
    if( pWaitSem != NULL )
    {
        IotSemaphore_Post( pWaitSem );

        /* Yield the processor to context switch. */
        IotClock_SleepMs( 10 );
    }

    /* This function returns the message length to simulate a successful send. */
    return messageLength;
}

/*-----------------------------------------------------------*/

/**
 * @brief A send function for PINGREQ that responds with a PINGRESP.
 */
static size_t _sendPingreq( IotNetworkConnection_t pSendContext,
                            const uint8_t * pMessage,
                            size_t messageLength )
{
    /* Silence warnings about unused parameters. */
    ( void ) pSendContext;
    ( void ) pMessage;

    /* Create a thread that responds with PINGRESP, then increment the PINGREQ
     * send counter if successful. */
    if( Iot_CreateDetachedThread( _incomingPingresp,
                                  NULL,
                                  IOT_THREAD_DEFAULT_PRIORITY,
                                  IOT_THREAD_DEFAULT_STACK_SIZE ) == true )
    {
        _pingreqSendCount++;
    }

    /* This function returns the message length to simulate a successful send. */
    return messageLength;
}

/*-----------------------------------------------------------*/

/**
 * @brief A send function that delays.
 */
static size_t _sendDelay( IotNetworkConnection_t pSendContext,
                          const uint8_t * pMessage,
                          size_t messageLength )
{
    IotSemaphore_t * pWaitSem = ( IotSemaphore_t * ) pSendContext;

    /* Silence warnings about unused parameters. */
    ( void ) pMessage;

    /* Post to the wait semaphore. */
    IotSemaphore_Post( pWaitSem );

    /* Delay for 2 seconds. */
    IotClock_SleepMs( 2000 );

    /* This function returns the message length to simulate a successful send. */
    return messageLength;
}

/*-----------------------------------------------------------*/

/**
 * @brief A create function that fails when server info is not supplied.
 */
static IotNetworkError_t _createMock( IotNetworkServerInfo_t pServerInfo,
                                      IotNetworkCredentials_t pCredentialInfo,
                                      IotNetworkConnection_t * pConnection )
{
    ( void ) pCredentialInfo;
    ( void ) pConnection;

    if( pServerInfo == NULL )
    {
        return IOT_NETWORK_FAILURE;
    }
    else
    {
        return IOT_NETWORK_SUCCESS;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief An empty function for task pool job.
 */
static void _testTaskRoutine( IotTaskPool_t pTaskPool,
                              IotTaskPoolJob_t pJob,
                              void * pUserContext )
{
    /* Do Nothing */
    ( void ) pTaskPool;
    ( void ) pJob;
    ( void ) pUserContext;
}

/*-----------------------------------------------------------*/

/**
 * @brief This send function checks that a duplicate outgoing message differs from
 * the original.
 */
static size_t _dupChecker( IotNetworkConnection_t pSendContext,
                           const uint8_t * pMessage,
                           size_t messageLength )
{
    static int32_t runCount = 0;
    static bool status = true;
    bool * pDupCheckResult = ( bool * ) pSendContext;
    uint8_t publishFlags = *pMessage;

    /* Declare the remaining variables required to check packet identifier
     * for the AWS IoT MQTT server. */
    #if AWS_IOT_MQTT_SERVER == true
        static uint16_t lastPacketIdentifier = 0;
        _mqttPacket_t publishPacket = { .u.pMqttConnection = NULL };
        _mqttOperation_t publishOperation = { .link = { 0 } };

        publishPacket.type = publishFlags;
        publishPacket.u.pIncomingPublish = &publishOperation;
        publishPacket.remainingLength = 8 + TEST_TOPIC_NAME_LENGTH;
        publishPacket.pRemainingData = ( uint8_t * ) pMessage + ( messageLength - publishPacket.remainingLength );
    #endif

    /* Ignore any MQTT packet that's not a PUBLISH. */
    if( ( publishFlags & 0xf0 ) != MQTT_PACKET_TYPE_PUBLISH )
    {
        return messageLength;
    }

    runCount++;

    /* Check how many times this function has been called. */
    if( runCount == 1 )
    {
        #if AWS_IOT_MQTT_SERVER == true
            /* Deserialize the PUBLISH to read the packet identifier. */
            if( _IotMqtt_DeserializePublish( &publishPacket ) != IOT_MQTT_SUCCESS )
            {
                status = false;
            }
            else
            {
                lastPacketIdentifier = publishPacket.packetIdentifier;
            }
        #else /* if AWS_IOT_MQTT_SERVER == true */
            /* DUP flag should not be set on this function's first run. */
            if( ( publishFlags & 0x08 ) == 0x08 )
            {
                status = false;
            }
        #endif /* if AWS_IOT_MQTT_SERVER == true */
    }
    else
    {
        /* Only check the packet again if the previous run checks passed. */
        if( status == true )
        {
            #if AWS_IOT_MQTT_SERVER == true
                /* Deserialize the PUBLISH to read the packet identifier. */
                if( _IotMqtt_DeserializePublish( &publishPacket ) != IOT_MQTT_SUCCESS )
                {
                    status = false;
                }
                else
                {
                    /* Check that the packet identifier is different. */
                    status = ( publishPacket.packetIdentifier != lastPacketIdentifier );
                    lastPacketIdentifier = publishPacket.packetIdentifier;
                }
            #else /* if AWS_IOT_MQTT_SERVER == true */
                /* DUP flag should be set when this function runs again. */
                if( ( publishFlags & 0x08 ) != 0x08 )
                {
                    status = false;
                }
            #endif /* if AWS_IOT_MQTT_SERVER == true */
        }

        /* Write the check result on the last expected run of this function. */
        if( runCount == DUP_CHECK_RETRY_LIMIT )
        {
            *pDupCheckResult = status;
        }
    }

    /* Return the message length to simulate a successful send. */
    return messageLength;
}

/*-----------------------------------------------------------*/

/**
 * @brief A network receive function that simulates receiving a PINGRESP.
 */
static size_t _receivePingresp( IotNetworkConnection_t pReceiveContext,
                                uint8_t * pBuffer,
                                size_t bytesRequested )
{
    size_t bytesReceived = 0;
    static size_t receiveIndex = 0;
    const uint8_t pPingresp[ 2 ] = { MQTT_PACKET_TYPE_PINGRESP, 0x00 };

    /* Silence warnings about unused parameters. */
    ( void ) pReceiveContext;

    /* Receive of PINGRESP should only ever request 1 byte. */
    if( bytesRequested == 1 )
    {
        /* Write a byte of PINGRESP. */
        *pBuffer = pPingresp[ receiveIndex ];
        bytesReceived = 1;

        /* Alternate the byte of PINGRESP to write. */
        receiveIndex = ( receiveIndex + 1 ) % 2;
    }

    return bytesReceived;
}

/*-----------------------------------------------------------*/

/**
 * @brief A function for setting the receive callback that just returns success.
 */
static IotNetworkError_t _setReceiveCallback( IotNetworkConnection_t pConnection,
                                              IotNetworkReceiveCallback_t receiveCallback,
                                              void * pReceiveContext )
{
    /* Silence warnings about unused parameters. */
    ( void ) pConnection;
    ( void ) receiveCallback;
    ( void ) pReceiveContext;

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

/**
 * @brief A network close function that counts how many times it was invoked.
 */
static IotNetworkError_t _close( IotNetworkConnection_t pCloseContext )
{
    /* Silence warnings about unused parameters. */
    ( void ) pCloseContext;

    Atomic_Increment_u32( &_closeCount );

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

/**
 * @brief An MQTT disconnect callback that counts how many times it was invoked.
 */
static void _disconnectCallback( void * pCallbackContext,
                                 IotMqttCallbackParam_t * pCallbackParam )
{
    IotMqttDisconnectReason_t * pExpectedReason = ( IotMqttDisconnectReason_t * ) pCallbackContext;

    /* Only increment counter if the reasons match. */
    if( pCallbackParam->u.disconnectReason == *pExpectedReason )
    {
        Atomic_Increment_u32( &_disconnectCallbackCount );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief A task pool job routine that decrements an MQTT operation's job
 * reference count.
 */
static void _decrementReferencesJob( IotTaskPool_t pTaskPool,
                                     IotTaskPoolJob_t pJob,
                                     void * pContext )
{
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) pContext;

    /* Silence warnings about unused parameters. */
    ( void ) pTaskPool;
    ( void ) pJob;

    /* Decrement an operation's reference count. */
    if( _IotMqtt_DecrementOperationReferences( pOperation, false ) == false )
    {
        /* Unblock the main test thread. */
        IotSemaphore_Post( &( pOperation->u.operation.notify.waitSemaphore ) );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief get next byte mock function to test MQTT serializer API
 */
static IotMqttError_t _getNextByte( void * pNetworkInterface,
                                    uint8_t * nextByte )
{
    uint8_t * buffer;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Treat network interface as pointer to buffer for mocking  */
    /* Send next byte */
    if( ( pNetworkInterface != NULL ) && ( nextByte != NULL ) )
    {
        buffer = ( *( uint8_t ** ) pNetworkInterface );
        /*  read single byte */
        *nextByte = *buffer;
        /* Move stream by 1 byte */
        ( *( uint8_t ** ) pNetworkInterface ) = ++buffer;
    }
    else
    {
        status = IOT_MQTT_NETWORK_ERROR;
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for MQTT API tests.
 */
TEST_GROUP( MQTT_Unit_API );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for MQTT API tests.
 */
TEST_SETUP( MQTT_Unit_API )
{
    _publishSetDupCalled = false;
    _pingreqSendCount = 0;

    /* Reset the network info and interface. */
    ( void ) memset( &_networkInfo, 0x00, sizeof( IotMqttNetworkInfo_t ) );
    ( void ) memset( &_networkInterface, 0x00, sizeof( IotNetworkInterface_t ) );
    _networkInterface.setReceiveCallback = _setReceiveCallback;
    _networkInfo.pNetworkInterface = &_networkInterface;

    /* Reset the counters. */
    _pingreqSendCount = 0;
    _closeCount = 0;
    _disconnectCallbackCount = 0;

    /* Initialize libraries. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for MQTT API tests.
 */
TEST_TEAR_DOWN( MQTT_Unit_API )
{
    IotMqtt_Cleanup();
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for MQTT API tests.
 */
TEST_GROUP_RUNNER( MQTT_Unit_API )
{
    RUN_TEST_CASE( MQTT_Unit_API, Init );
    RUN_TEST_CASE( MQTT_Unit_API, StringCoverage );
    RUN_TEST_CASE( MQTT_Unit_API, OperationCreateDestroy );
    RUN_TEST_CASE( MQTT_Unit_API, OperationWaitTimeout );
    RUN_TEST_CASE( MQTT_Unit_API, ConnectParameters );
    RUN_TEST_CASE( MQTT_Unit_API, ConnectMallocFail );
    RUN_TEST_CASE( MQTT_Unit_API, ConnectRestoreSessionMallocFail );
    RUN_TEST_CASE( MQTT_Unit_API, DisconnectMallocFail );
    RUN_TEST_CASE( MQTT_Unit_API, DisconnectAlreadyDisconnected );
    RUN_TEST_CASE( MQTT_Unit_API, PublishQoS0Parameters );
    RUN_TEST_CASE( MQTT_Unit_API, PublishQoS0MallocFail );
    RUN_TEST_CASE( MQTT_Unit_API, PublishQoS1 );
    RUN_TEST_CASE( MQTT_Unit_API, PublishDuplicates );
    RUN_TEST_CASE( MQTT_Unit_API, SubscribeUnsubscribeParameters );
    RUN_TEST_CASE( MQTT_Unit_API, SubscribeMallocFail );
    RUN_TEST_CASE( MQTT_Unit_API, UnsubscribeMallocFail );
    RUN_TEST_CASE( MQTT_Unit_API, SingleThreaded );
    RUN_TEST_CASE( MQTT_Unit_API, KeepAlivePeriodic );
    RUN_TEST_CASE( MQTT_Unit_API, KeepAliveJobCleanup );
    RUN_TEST_CASE( MQTT_Unit_API, GetConnectPacketSizeChecks );
    RUN_TEST_CASE( MQTT_Unit_API, SerializeConnectChecks );
    RUN_TEST_CASE( MQTT_Unit_API, GetSubscribePacketSizeChecks );
    RUN_TEST_CASE( MQTT_Unit_API, SerializeSubscribeChecks );
    RUN_TEST_CASE( MQTT_Unit_API, SerializeUnsubscribeChecks );
    RUN_TEST_CASE( MQTT_Unit_API, GetPublishPacketSizeChecks );
    RUN_TEST_CASE( MQTT_Unit_API, SerializePublishChecks );
    RUN_TEST_CASE( MQTT_Unit_API, SerializeDisconnectChecks );
    RUN_TEST_CASE( MQTT_Unit_API, SerializePingReqChecks );
    RUN_TEST_CASE( MQTT_Unit_API, DeserializeResponseChecks );
    RUN_TEST_CASE( MQTT_Unit_API, DeserializePublishChecks );
    RUN_TEST_CASE( MQTT_Unit_API, GetIncomingMQTTPacketTypeAndLengthChecks );
    RUN_TEST_CASE( MQTT_Unit_API, MqttOperationTryDestroy );
    RUN_TEST_CASE( MQTT_Unit_API, CreateNetworkConnectionCheck );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the function @ref mqtt_function_init.
 */
TEST( MQTT_Unit_API, Init )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttOperation_t operation = IOT_MQTT_OPERATION_INITIALIZER;

    /* Initialization was done in test set up. Clean up here before running this test. */
    IotMqtt_Cleanup();

    /* Calling cleanup twice should not crash. */
    IotMqtt_Cleanup();

    /* Calling API functions without calling IotMqtt_Init should fail. */
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_NOT_INITIALIZED, status );

    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK;
    status = IotMqtt_SubscribeAsync( _pMqttConnection, &subscription, 1, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_NOT_INITIALIZED, status );

    status = IotMqtt_UnsubscribeAsync( _pMqttConnection, &subscription, 1, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_NOT_INITIALIZED, status );

    publishInfo.pTopicName = TEST_TOPIC_NAME;
    publishInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;
    status = IotMqtt_PublishAsync( _pMqttConnection, &publishInfo, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_NOT_INITIALIZED, status );

    status = IotMqtt_Wait( operation, TIMEOUT_MS );
    TEST_ASSERT_EQUAL( IOT_MQTT_NOT_INITIALIZED, status );

    IotMqtt_Disconnect( _pMqttConnection, 0 );

    /* Reinitialize for test cleanup. Calling init twice should not crash. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );
}

/*-----------------------------------------------------------*/

/**
 * @brief Provides code coverage of the MQTT enum-to-string functions,
 * @ref mqtt_function_strerror and @ref mqtt_function_operationtype.
 */
TEST( MQTT_Unit_API, StringCoverage )
{
    int32_t i = 0;
    const char * pMessage = NULL;

    /* For each MQTT Error, check the returned string. */
    const char * pExitString = "INVALID STATUS";
    size_t exitStringLength = strlen( pExitString );

    while( true )
    {
        pMessage = IotMqtt_strerror( ( IotMqttError_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( pExitString, pMessage, exitStringLength ) == 0 )
        {
            break;
        }

        i++;
    }

    /* For each MQTT Operation Type, check the returned string. */
    i = 0;
    pExitString = "INVALID OPERATION";
    exitStringLength = strlen( pExitString );

    while( true )
    {
        pMessage = IotMqtt_OperationType( ( IotMqttOperationType_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( pExitString, pMessage, exitStringLength ) == 0 )
        {
            break;
        }

        i++;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Test reference counts as MQTT operations are created and destroyed.
 */
TEST( MQTT_Unit_API, OperationCreateDestroy )
{
    _mqttOperation_t * pOperation = NULL;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Adjustment to reference count based on keep-alive status. */
    const int32_t keepAliveReference = 1 + ( ( _pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0 ) ? 1 : 0 );

    /* A new MQTT connection should only have a possible reference for keep-alive. */
    TEST_ASSERT_EQUAL_INT32( keepAliveReference, _pMqttConnection->references );

    /* Create a new operation referencing the MQTT connection. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_CreateOperation( _pMqttConnection,
                                                                   IOT_MQTT_FLAG_WAITABLE,
                                                                   NULL,
                                                                   &pOperation ) );

    /* Check reference counts and list placement. */
    TEST_ASSERT_EQUAL_INT32( 1 + keepAliveReference, _pMqttConnection->references );
    TEST_ASSERT_EQUAL_INT32( 2, pOperation->u.operation.jobReference );
    TEST_ASSERT_EQUAL_PTR( &( pOperation->link ), IotListDouble_FindFirstMatch( &( _pMqttConnection->pendingProcessing ),
                                                                                NULL,
                                                                                NULL,
                                                                                &( pOperation->link ) ) );

    /* Schedule a job that destroys the operation. */
    TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS, IotTaskPool_CreateJob( _decrementReferencesJob,
                                                                    pOperation,
                                                                    &( pOperation->jobStorage ),
                                                                    &( pOperation->job ) ) );
    TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS, IotTaskPool_Schedule( IOT_SYSTEM_TASKPOOL,
                                                                   pOperation->job,
                                                                   0 ) );

    /* Wait for the job to complete. */
    IotSemaphore_Wait( &( pOperation->u.operation.notify.waitSemaphore ) );

    /* Check reference counts after job completion. */
    TEST_ASSERT_EQUAL_INT32( 1 + keepAliveReference, _pMqttConnection->references );
    TEST_ASSERT_EQUAL_INT32( 1, pOperation->u.operation.jobReference );
    TEST_ASSERT_EQUAL_PTR( &( pOperation->link ), IotListDouble_FindFirstMatch( &( _pMqttConnection->pendingProcessing ),
                                                                                NULL,
                                                                                NULL,
                                                                                &( pOperation->link ) ) );

    /* Disconnect the MQTT connection, then call Wait to clean up the operation. */
    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
    IotMqtt_Wait( pOperation, 0 );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that an operation is correctly cleaned up if @ref mqtt_function_wait
 * times out while its job is executing.
 */
TEST( MQTT_Unit_API, OperationWaitTimeout )
{
    _mqttOperation_t * pOperation = NULL;
    IotSemaphore_t waitSem;

    /* An arbitrary MQTT packet for this test. */
    static uint8_t pPacket[ 2 ] = { MQTT_PACKET_TYPE_PINGREQ, 0x00 };

    /* Create the wait semaphore. */
    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &waitSem, 0, 1 ) );

    if( TEST_PROTECT() )
    {
        /* Set the network interface send function. */
        _networkInterface.send = _sendDelay;

        /* Create a new MQTT connection. */
        _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                             &_networkInfo,
                                                             0 );
        TEST_ASSERT_NOT_NULL( _pMqttConnection );

        /* Set parameter to network send function. */
        _pMqttConnection->pNetworkConnection = &waitSem;

        /* Create a new operation referencing the MQTT connection. */
        TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_CreateOperation( _pMqttConnection,
                                                                       IOT_MQTT_FLAG_WAITABLE,
                                                                       NULL,
                                                                       &pOperation ) );

        /* Set an arbitrary MQTT packet for the operation. */
        pOperation->u.operation.type = IOT_MQTT_PINGREQ;
        pOperation->u.operation.pMqttPacket = pPacket;
        pOperation->u.operation.packetSize = 2;

        /* Schedule the send job. */
        TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, _IotMqtt_ScheduleOperation( pOperation,
                                                                         _IotMqtt_ProcessSend,
                                                                         0 ) );

        /* Wait for the send job to begin. */
        IotSemaphore_Wait( &waitSem );

        /* Wait on the MQTT operation with a short timeout. This should cause a
         * timeout while the send job is still executing. */
        TEST_ASSERT_EQUAL( IOT_MQTT_TIMEOUT, IotMqtt_Wait( pOperation, 10 ) );

        /* Wait with an invalid operation */
        TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, IotMqtt_Wait( NULL, 10 ) );

        /* Check reference count after a timed out wait. */
        IotMutex_Lock( &( _pMqttConnection->referencesMutex ) );
        TEST_ASSERT_EQUAL_INT32( 1, pOperation->u.operation.jobReference );
        IotMutex_Unlock( &( _pMqttConnection->referencesMutex ) );

        /* Disconnect the MQTT connection. */
        IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );

        /* Clean up the MQTT library, which waits for the send job to finish. The
         * library must be re-initialized so that test tear down does not crash. */
        IotMqtt_Cleanup();
        IotMqtt_Init();
    }

    IotSemaphore_Destroy( &waitSem );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_connect with various
 * invalid parameters.
 */
TEST( MQTT_Unit_API, ConnectParameters )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttPublishInfo_t willInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;

    _networkInterface.send = _sendSuccess;
    _networkInterface.close = _close;

    /* Check that the network interface is validated. */
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

    /* Check that the connection info is validated. */
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

    /* Connect with bad previous session subscription. */
    connectInfo.cleanSession = false;
    connectInfo.pPreviousSubscriptions = &subscription;
    connectInfo.previousSubscriptionCount = 1;
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

    /* Connect with bad subscription count. */
    connectInfo.previousSubscriptionCount = 0;
    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK;
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
    connectInfo.previousSubscriptionCount = 1;

    /* Check that the will info is validated when it's provided. */
    connectInfo.pWillInfo = &willInfo;
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
    willInfo.pTopicName = TEST_TOPIC_NAME;
    willInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;

    /* Check that a will message longer than 65535 is not allowed. */
    willInfo.pPayload = "";
    willInfo.payloadLength = 65536;
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
    willInfo.payloadLength = 0;

    /* Check connect returns error if network info is invalid. */
    status = IotMqtt_Connect( NULL,
                              &connectInfo,
                              TIMEOUT_MS,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_NETWORK_ERROR, status );

    /* Check that passing a wait time of 0 returns immediately. */
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              0,
                              &_pMqttConnection );
    TEST_ASSERT_EQUAL( IOT_MQTT_TIMEOUT, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_connect when memory
 * allocation fails at various points.
 */
TEST( MQTT_Unit_API, ConnectMallocFail )
{
    int32_t i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;
    _networkInterface.close = _close;
    connectInfo.keepAliveSeconds = 100;
    connectInfo.cleanSession = true;
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call CONNECT. Memory allocation will fail at various times during
         * this call. */
        status = IotMqtt_Connect( &_networkInfo,
                                  &connectInfo,
                                  TIMEOUT_MS,
                                  &_pMqttConnection );

        /* If the return value is timeout, then all memory allocation succeeded
         * and the loop can exit. The expected return value is timeout (and not
         * success) because the receive callback is never invoked. */
        if( status == IOT_MQTT_TIMEOUT )
        {
            break;
        }

        /* If the return value isn't timeout, check that it is memory allocation
         * failure. */
        TEST_ASSERT_EQUAL( IOT_MQTT_NO_MEMORY, status );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_connect when memory
 * allocation fails at various points for a persistent session.
 */
TEST( MQTT_Unit_API, ConnectRestoreSessionMallocFail )
{
    int32_t i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;
    _networkInterface.close = _close;
    connectInfo.cleanSession = false;
    connectInfo.keepAliveSeconds = 100;
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;
    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK;

    connectInfo.pPreviousSubscriptions = &subscription;
    connectInfo.previousSubscriptionCount = 1;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call CONNECT with a previous session. Memory allocation will fail at
         * various times during this call. */
        status = IotMqtt_Connect( &_networkInfo,
                                  &connectInfo,
                                  TIMEOUT_MS,
                                  &_pMqttConnection );

        /* If the return value is timeout, then all memory allocation succeeded
         * and the loop can exit. The expected return value is timeout (and not
         * success) because the receive callback is never invoked. */
        if( status == IOT_MQTT_TIMEOUT )
        {
            break;
        }

        /* If the return value isn't timeout, check that it is memory allocation
         * failure. */
        TEST_ASSERT_EQUAL( IOT_MQTT_NO_MEMORY, status );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_disconnect when memory
 * allocation fails at various points.
 */
TEST( MQTT_Unit_API, DisconnectMallocFail )
{
    int32_t i = 0;
    IotMqttDisconnectReason_t expectedReason = IOT_MQTT_DISCONNECT_CALLED;

    /* Set the members of the network interface. */
    _networkInterface.send = _sendSuccess;
    _networkInterface.close = _close;
    _networkInfo.createNetworkConnection = false;
    _networkInfo.disconnectCallback.pCallbackContext = &expectedReason;
    _networkInfo.disconnectCallback.function = _disconnectCallback;

    for( i = 0; i < DISCONNECT_MALLOC_LIMIT; i++ )
    {
        /* Allow unlimited use of malloc during connection initialization. */
        UnityMalloc_MakeMallocFailAfterCount( -1 );

        /* Create a new MQTT connection. */
        _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                             &_networkInfo,
                                                             0 );
        TEST_ASSERT_NOT_NULL( _pMqttConnection );

        /* Set malloc to eventually fail. */
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call DISCONNECT; this function should always perform cleanup regardless
         * of memory allocation errors. */
        IotMqtt_Disconnect( _pMqttConnection, 0 );
        TEST_ASSERT_EQUAL_INT( 1, _closeCount );
        TEST_ASSERT_EQUAL_INT( 1, _disconnectCallbackCount );
        _closeCount = 0;
        _disconnectCallbackCount = 0;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_disconnect when
 * disconnected mqtt connection is passed.
 */
TEST( MQTT_Unit_API, DisconnectAlreadyDisconnected )
{
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

    /* Set up a mocked MQTT connection. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &mqttConnection ) );
    TEST_ASSERT_EQUAL_INT( 1, mqttConnection->references );

    /* Increase reference count to 3 so the subsequent disconnect
     * calls do not free the connection. */
    mqttConnection->references += 2;
    /* Call Disconnect, reference count should decrement. */
    IotMqtt_Disconnect( mqttConnection, 0 );
    TEST_ASSERT_EQUAL_INT( 2, mqttConnection->references );
    /* 'disconnected' flag should be set */
    TEST_ASSERT_EQUAL( true, mqttConnection->disconnected );

    /* Make sure reference count is decremented when 'disconnected'
     * connection is passed without any attempts to close socket again. */
    IotMqtt_Disconnect( mqttConnection, 0 );
    TEST_ASSERT_EQUAL_INT( 1, mqttConnection->references );

    /* One final disconnect to bring reference count to zero and free
     * the connection */
    IotMqtt_Disconnect( mqttConnection, 0 );

    /* mqttConnection should be freed after above call.
     * Test should not fail with any Unity memory leak asserts. */
}
/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_publishasync (QoS 0) with various
 * valid and invalid parameters.
 */
TEST( MQTT_Unit_API, PublishQoS0Parameters )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttOperation_t publishOperation = IOT_MQTT_OPERATION_INITIALIZER;
    IotMqttCallbackInfo_t callbackInfo = IOT_MQTT_CALLBACK_INFO_INITIALIZER;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    if( TEST_PROTECT() )
    {
        /* Check that the publish info is validated. */
        status = IotMqtt_PublishAsync( _pMqttConnection, &publishInfo, 0, NULL, NULL );
        TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
        publishInfo.pTopicName = TEST_TOPIC_NAME;
        publishInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;

        /* Check that a QoS 0 publish is refused if a notification is requested. */
        status = IotMqtt_PublishAsync( _pMqttConnection, &publishInfo, IOT_MQTT_FLAG_WAITABLE, NULL, &publishOperation );
        TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );
        status = IotMqtt_PublishAsync( _pMqttConnection, &publishInfo, 0, &callbackInfo, NULL );
        TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

        /* If valid parameters are passed, QoS 0 publish should always return success. */
        status = IotMqtt_PublishAsync( _pMqttConnection, &publishInfo, 0, 0, &publishOperation );
        TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, status );
    }

    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_publishasync (QoS 0) when memory
 * allocation fails at various points.
 */
TEST( MQTT_Unit_API, PublishQoS0MallocFail )
{
    int32_t i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Set the necessary members of publish info. */
    publishInfo.pTopicName = TEST_TOPIC_NAME;
    publishInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;

    if( TEST_PROTECT() )
    {
        for( i = 0; ; i++ )
        {
            UnityMalloc_MakeMallocFailAfterCount( i );

            /* Call PUBLISH. Memory allocation will fail at various times during
             * this call. */
            status = IotMqtt_PublishAsync( _pMqttConnection, &publishInfo, 0, NULL, NULL );

            /* Once PUBLISH succeeds, the loop can exit. */
            if( status == IOT_MQTT_SUCCESS )
            {
                break;
            }

            /* If the return value isn't success, check that it is memory allocation
             * failure. */
            TEST_ASSERT_EQUAL( IOT_MQTT_NO_MEMORY, status );
        }
    }

    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_publishasync (QoS 1) with various
 * invalid parameters. Also tests the behavior of @ref mqtt_function_publishasync
 * (QoS 1) when memory allocation fails at various points.
 */
TEST( MQTT_Unit_API, PublishQoS1 )
{
    int32_t i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttOperation_t publishOperation = IOT_MQTT_OPERATION_INITIALIZER;
    IotMqttCallbackInfo_t callbackInfo = IOT_MQTT_CALLBACK_INFO_INITIALIZER;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Set the publish info. */
    publishInfo.qos = IOT_MQTT_QOS_1;
    publishInfo.pTopicName = TEST_TOPIC_NAME;
    publishInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;

    if( TEST_PROTECT() )
    {
        /* Setting the waitable flag with no reference is not allowed. */
        status = IotMqtt_PublishAsync( _pMqttConnection,
                                       &publishInfo,
                                       IOT_MQTT_FLAG_WAITABLE,
                                       NULL,
                                       NULL );
        TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

        /* Setting both the waitable flag and callback info is not allowed. */
        status = IotMqtt_PublishAsync( _pMqttConnection,
                                       &publishInfo,
                                       IOT_MQTT_FLAG_WAITABLE,
                                       &callbackInfo,
                                       &publishOperation );
        TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

        /* Check QoS 1 PUBLISH behavior with malloc failures. */
        for( i = 0; ; i++ )
        {
            UnityMalloc_MakeMallocFailAfterCount( i );

            /* Call PUBLISH. Memory allocation will fail at various times during
             * this call. */
            status = IotMqtt_PublishAsync( _pMqttConnection,
                                           &publishInfo,
                                           IOT_MQTT_FLAG_WAITABLE,
                                           NULL,
                                           &publishOperation );

            /* If the PUBLISH succeeded, the loop can exit after waiting for the QoS
             * 1 PUBLISH to be cleaned up. */
            if( status == IOT_MQTT_STATUS_PENDING )
            {
                TEST_ASSERT_EQUAL( IOT_MQTT_TIMEOUT, IotMqtt_Wait( publishOperation, TIMEOUT_MS ) );
                break;
            }

            /* If the return value isn't success, check that it is memory allocation
             * failure. */
            TEST_ASSERT_EQUAL( IOT_MQTT_NO_MEMORY, status );
        }
    }

    /* Clean up MQTT connection. */
    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that duplicate QoS 1 PUBLISH packets are different from the
 * original.
 *
 * For non-AWS IoT MQTT servers, checks that the DUP flag is set. For
 * AWS IoT MQTT servers, checks that the packet identifier is different.
 */
TEST( MQTT_Unit_API, PublishDuplicates )
{
    static IotMqttSerializer_t serializer = IOT_MQTT_SERIALIZER_INITIALIZER;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttOperation_t publishOperation = IOT_MQTT_OPERATION_INITIALIZER;
    bool dupCheckResult = false;
    uint64_t startTime = 0;

    /* Initializer parameters. */
    serializer.serialize.publishSetDup = _publishSetDup;
    _networkInterface.send = _dupChecker;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Set the serializers and parameter to the send function. */
    _pMqttConnection->pNetworkConnection = &dupCheckResult;
    _pMqttConnection->pSerializer = &serializer;

    /* Set the publish info. */
    publishInfo.qos = IOT_MQTT_QOS_1;
    publishInfo.pTopicName = TEST_TOPIC_NAME;
    publishInfo.topicNameLength = TEST_TOPIC_NAME_LENGTH;
    publishInfo.pPayload = "test";
    publishInfo.payloadLength = 4;
    publishInfo.retryMs = DUP_CHECK_RETRY_MS;
    publishInfo.retryLimit = DUP_CHECK_RETRY_LIMIT;

    startTime = IotClock_GetTimeMs();

    if( TEST_PROTECT() )
    {
        /* Send a PUBLISH with retransmissions enabled. */
        TEST_ASSERT_EQUAL( IOT_MQTT_STATUS_PENDING,
                           IotMqtt_PublishAsync( _pMqttConnection,
                                                 &publishInfo,
                                                 IOT_MQTT_FLAG_WAITABLE,
                                                 NULL,
                                                 &publishOperation ) );

        /* Since _dupChecker doesn't actually transmit a PUBLISH, no PUBACK is
         * expected. */
        TEST_ASSERT_EQUAL( IOT_MQTT_RETRY_NO_RESPONSE,
                           IotMqtt_Wait( publishOperation, DUP_CHECK_TIMEOUT ) );

        /* Check the result of the DUP check. */
        TEST_ASSERT_EQUAL_INT( true, dupCheckResult );

        /* Check that at least the minimum wait time elapsed. */
        TEST_ASSERT_TRUE( startTime + DUP_CHECK_MINIMUM_WAIT <= IotClock_GetTimeMs() );
    }

    /* Clean up MQTT connection. */
    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );

    /* Check that the set DUP override was called. */
    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL_INT( true, _publishSetDupCalled );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_subscribeasync and
 * @ref mqtt_function_unsubscribeasync with various invalid parameters.
 */
TEST( MQTT_Unit_API, SubscribeUnsubscribeParameters )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttOperation_t subscribeOperation = IOT_MQTT_OPERATION_INITIALIZER;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Check that subscription info is validated. */
    status = IotMqtt_SubscribeAsync( _pMqttConnection,
                                     &subscription,
                                     1,
                                     IOT_MQTT_FLAG_WAITABLE,
                                     NULL,
                                     &subscribeOperation );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_UnsubscribeAsync( _pMqttConnection,
                                       &subscription,
                                       1,
                                       IOT_MQTT_FLAG_WAITABLE,
                                       NULL,
                                       &subscribeOperation );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK;

    /* A reference must be provided for a waitable SUBSCRIBE. */
    status = IotMqtt_SubscribeAsync( _pMqttConnection,
                                     &subscription,
                                     1,
                                     IOT_MQTT_FLAG_WAITABLE,
                                     NULL,
                                     NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_UnsubscribeAsync( _pMqttConnection,
                                       &subscription,
                                       1,
                                       IOT_MQTT_FLAG_WAITABLE,
                                       NULL,
                                       NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_PARAMETER, status );

    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_subscribeasync when memory allocation
 * fails at various points.
 */
TEST( MQTT_Unit_API, SubscribeMallocFail )
{
    int32_t i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttOperation_t subscribeOperation = IOT_MQTT_OPERATION_INITIALIZER;

    /* Initializer parameters. */
    _networkInterface.send = _sendSuccess;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Set the necessary members of the subscription. */
    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK;

    if( TEST_PROTECT() )
    {
        for( i = 0; ; i++ )
        {
            UnityMalloc_MakeMallocFailAfterCount( i );

            /* Call SUBSCRIBE. Memory allocation will fail at various times during
             * this call. */
            status = IotMqtt_SubscribeAsync( _pMqttConnection,
                                             &subscription,
                                             1,
                                             IOT_MQTT_FLAG_WAITABLE,
                                             NULL,
                                             &subscribeOperation );

            /* If the SUBSCRIBE succeeded, the loop can exit after waiting for
             * the SUBSCRIBE to be cleaned up. */
            if( status == IOT_MQTT_STATUS_PENDING )
            {
                TEST_ASSERT_EQUAL( IOT_MQTT_TIMEOUT, IotMqtt_Wait( subscribeOperation, TIMEOUT_MS ) );
                break;
            }

            /* If the return value isn't success, check that it is memory allocation
             * failure. */
            TEST_ASSERT_EQUAL( IOT_MQTT_NO_MEMORY, status );
        }

        /* No lingering subscriptions should be in the MQTT connection. */
        TEST_ASSERT_EQUAL_INT( true, IotListDouble_IsEmpty( &( _pMqttConnection->subscriptionList ) ) );
    }

    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_unsubscribeasync when memory
 * allocation fails at various points.
 */
TEST( MQTT_Unit_API, UnsubscribeMallocFail )
{
    int32_t i = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    IotMqttOperation_t unsubscribeOperation = IOT_MQTT_OPERATION_INITIALIZER;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         0 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Set the necessary members of the subscription. */
    subscription.pTopicFilter = TEST_TOPIC_NAME;
    subscription.topicFilterLength = TEST_TOPIC_NAME_LENGTH;
    subscription.callback.function = SUBSCRIPTION_CALLBACK;

    if( TEST_PROTECT() )
    {
        for( i = 0; ; i++ )
        {
            UnityMalloc_MakeMallocFailAfterCount( i );

            /* Call UNSUBSCRIBE. Memory allocation will fail at various times during
             * this call. */
            status = IotMqtt_UnsubscribeAsync( _pMqttConnection,
                                               &subscription,
                                               1,
                                               IOT_MQTT_FLAG_WAITABLE,
                                               NULL,
                                               &unsubscribeOperation );

            /* If the UNSUBSCRIBE succeeded, the loop can exit after waiting for
             * the UNSUBSCRIBE to be cleaned up. */
            if( status == IOT_MQTT_STATUS_PENDING )
            {
                TEST_ASSERT_EQUAL( IOT_MQTT_TIMEOUT, IotMqtt_Wait( unsubscribeOperation, TIMEOUT_MS ) );
                break;
            }

            /* If the return value isn't success, check that it is memory allocation
             * failure. */
            TEST_ASSERT_EQUAL( IOT_MQTT_NO_MEMORY, status );
        }

        /* No lingering subscriptions should be in the MQTT connection. */
        TEST_ASSERT_EQUAL_INT( true, IotListDouble_IsEmpty( &( _pMqttConnection->subscriptionList ) ) );
    }

    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test that MQTT can work in a single thread without the task pool.
 */
TEST( MQTT_Unit_API, SingleThreaded )
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
    subscription.callback.function = SUBSCRIPTION_CALLBACK;

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
 * @brief Tests keep-alive handling and ensures that it is periodic.
 */
TEST( MQTT_Unit_API, KeepAlivePeriodic )
{
    /* The expected disconnect reason for this test's disconnect callback. */
    IotMqttDisconnectReason_t expectedReason = IOT_MQTT_KEEP_ALIVE_TIMEOUT;

    /* An estimate for the amount of time this test requires. */
    const uint32_t sleepTimeMs = ( KEEP_ALIVE_COUNT * SHORT_KEEP_ALIVE_MS ) +
                                 ( IOT_MQTT_RESPONSE_WAIT_MS * KEEP_ALIVE_COUNT ) + 2500;

    /* Print a newline so this test may log its status. */
    UNITY_PRINT_EOL();

    /* Initialize parameters. */
    _networkInterface.send = _sendPingreq;
    _networkInterface.receive = _receivePingresp;
    _networkInterface.close = _close;
    _networkInfo.disconnectCallback.pCallbackContext = &expectedReason;
    _networkInfo.disconnectCallback.function = _disconnectCallback;

    /* Create a new MQTT connection. */
    _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                         &_networkInfo,
                                                         1 );
    TEST_ASSERT_NOT_NULL( _pMqttConnection );

    /* Set a short keep-alive interval so this test runs faster. */
    _pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = SHORT_KEEP_ALIVE_MS;
    _pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs = SHORT_KEEP_ALIVE_MS;

    /* Schedule the initial PINGREQ. */
    TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS,
                       IotTaskPool_ScheduleDeferred( IOT_SYSTEM_TASKPOOL,
                                                     _pMqttConnection->pingreq.job,
                                                     _pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs ) );

    /* Sleep to allow ample time for periodic PINGREQ sends and PINGRESP responses. */
    IotClock_SleepMs( sleepTimeMs );

    /* Disconnect the connection. */
    IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );

    /* Check the counters for PINGREQ send and close. */
    TEST_ASSERT_EQUAL_INT32( KEEP_ALIVE_COUNT + 1, _pingreqSendCount );
    TEST_ASSERT_EQUAL_INT32( 2, _closeCount );

    /* Check that the disconnect callback was invoked once (with reason
     * "keep-alive timeout"). */
    TEST_ASSERT_EQUAL_INT32( 1, Atomic_Add_u32( &_disconnectCallbackCount, 0 ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that the keep-alive job cleans up the MQTT connection after a call
 * to @ref mqtt_function_disconnect.
 */
TEST( MQTT_Unit_API, KeepAliveJobCleanup )
{
    IotSemaphore_t waitSem;

    /* Initialize parameters. */
    _networkInterface.send = _sendSuccess;

    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &waitSem, 0, 1 ) );

    if( TEST_PROTECT() )
    {
        /* Create a new MQTT connection. */
        _pMqttConnection = IotTestMqtt_createMqttConnection( AWS_IOT_MQTT_SERVER,
                                                             &_networkInfo,
                                                             1 );
        TEST_ASSERT_NOT_NULL( _pMqttConnection );

        /* Set the parameter to the send function. */
        _pMqttConnection->pNetworkConnection = &waitSem;

        /* Set a short keep-alive interval so this test runs faster. */
        _pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = SHORT_KEEP_ALIVE_MS;
        _pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs = SHORT_KEEP_ALIVE_MS;

        /* Schedule the initial PINGREQ. */
        TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS,
                           IotTaskPool_ScheduleDeferred( IOT_SYSTEM_TASKPOOL,
                                                         _pMqttConnection->pingreq.job,
                                                         _pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs ) );

        /* Wait for the keep-alive job to send a PINGREQ. */
        IotSemaphore_Wait( &waitSem );

        /* Immediately disconnect the connection. */
        IotMqtt_Disconnect( _pMqttConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
    }

    IotSemaphore_Destroy( &waitSem );
}

/*-----------------------------------------------------------*/

/* Tests for public serializer API */

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_GetConnectPacketSize works as intended.
 * to @ref mqtt_function_getconnectpacketsize.
 */

TEST( MQTT_Unit_API, GetConnectPacketSizeChecks )
{
    IotMqttConnectInfo_t connectInfo;
    size_t remainingLength = 0;
    size_t packetSize = 0;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Call IotMqtt_GetConnectPacketSize() with various combinations of
     * incorrect paramters */

    status = IotMqtt_GetConnectPacketSize( NULL, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetConnectPacketSize( &connectInfo, NULL, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetConnectPacketSize( &connectInfo, &remainingLength, NULL );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Verify empty connect info fails. */
    memset( ( void * ) &connectInfo, 0x0, sizeof( connectInfo ) );
    status = IotMqtt_GetConnectPacketSize( &connectInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Verify good case */
    memset( ( void * ) &connectInfo, 0x0, sizeof( connectInfo ) );
    connectInfo.cleanSession = true;
    connectInfo.pClientIdentifier = "TEST";
    connectInfo.clientIdentifierLength = 4;
    status = IotMqtt_GetConnectPacketSize( &connectInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Make sure remaining size returned is 16. */
    TEST_ASSERT_EQUAL_INT( 16, remainingLength );
    /* Make sure packet size is 18. */
    TEST_ASSERT_EQUAL_INT( 18, packetSize );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_SerializeConnect works as intended.
 * to @ref mqtt_function_serializeconnect.
 */
TEST( MQTT_Unit_API, SerializeConnectChecks )
{
    IotMqttConnectInfo_t connectInfo;
    size_t remainingLength = 0;
    uint8_t buffer[ 20 ];
    size_t bufferSize = sizeof( buffer );
    size_t packetSize = bufferSize;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Verify bad parameter errors. */
    status = IotMqtt_SerializeConnect( NULL, remainingLength, buffer, packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );
    status = IotMqtt_SerializeConnect( &connectInfo, remainingLength, NULL, packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    memset( ( void * ) &connectInfo, 0x0, sizeof( connectInfo ) );
    /* Make sure greater remaining length returns error. */
    remainingLength = 120;
    status = IotMqtt_SerializeConnect( &connectInfo, 120, buffer, packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Good case succeeds */
    /* Calculate packet size. */
    memset( ( void * ) &connectInfo, 0x0, sizeof( connectInfo ) );
    connectInfo.cleanSession = true;
    connectInfo.pClientIdentifier = "TEST";
    connectInfo.clientIdentifierLength = 4;
    status = IotMqtt_GetConnectPacketSize( &connectInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Make sure buffer has enough space */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, bufferSize );
    /* Make sure test succeeds. */
    status = IotMqtt_SerializeConnect( &connectInfo, remainingLength, buffer, packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

    /* For this example, IotMqtt_GetConnectPacketSize() will return
     * packetSize = remainingLength +2 (two byte fixed header).
     * Make sure IotMqtt_SerializeConnect()
     * fails  when remaining length is more than packet size. */
    status = IotMqtt_SerializeConnect( &connectInfo, remainingLength + 4, buffer, packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_GetSubscribePacketSize works as intended.
 * to @ref mqtt_function_getsubscriptionpacketsize.
 */
TEST( MQTT_Unit_API, GetSubscribePacketSizeChecks )
{
    IotMqttSubscription_t subscriptionList;
    size_t subscriptionCount = 0;
    size_t remainingLength = 0;
    size_t packetSize = 0;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Verify parameters. */

    status = IotMqtt_GetSubscriptionPacketSize( 100,
                                                &subscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                NULL,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                &subscriptionList,
                                                subscriptionCount,
                                                NULL,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                &subscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                NULL );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );


    /* Verify empty subscription list fails.  */
    memset( ( void * ) &subscriptionList, 0x0, sizeof( subscriptionList ) );
    subscriptionCount = 0;
    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                &subscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Verify good case. */
    memset( ( void * ) &subscriptionList, 0x0, sizeof( subscriptionList ) );
    subscriptionList.qos = IOT_MQTT_QOS_0;
    subscriptionList.pTopicFilter = "/example/topic";
    subscriptionList.topicFilterLength = sizeof( "/example/topic" );
    subscriptionCount = sizeof( subscriptionList ) / sizeof( IotMqttSubscription_t );
    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                &subscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    TEST_ASSERT_GREATER_THAN( remainingLength, packetSize );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_SerializeSubscribe works as intended.
 * to @ref mqtt_function_serializesubscribe.
 */
TEST( MQTT_Unit_API, SerializeSubscribeChecks )
{
    IotMqttSubscription_t subscriptionList;
    size_t subscriptionCount = 0;
    size_t remainingLength = 0;
    uint16_t packetIdentifier;
    uint8_t buffer[ 25 ];
    size_t bufferSize = sizeof( buffer );
    size_t packetSize = bufferSize;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Verify bad parameters fail. */
    status = IotMqtt_SerializeSubscribe( NULL,
                                         subscriptionCount,
                                         remainingLength,
                                         &packetIdentifier,
                                         buffer,
                                         packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_SerializeSubscribe( &subscriptionList,
                                         subscriptionCount,
                                         remainingLength,
                                         NULL,
                                         buffer,
                                         packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_SerializeSubscribe( &subscriptionList,
                                         subscriptionCount,
                                         remainingLength,
                                         &packetIdentifier,
                                         NULL,
                                         packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Get correct values of packet size and remaining length. */
    memset( ( void * ) &subscriptionList, 0x0, sizeof( subscriptionList ) );
    subscriptionList.qos = IOT_MQTT_QOS_0;
    subscriptionList.pTopicFilter = "/example/topic";
    subscriptionList.topicFilterLength = sizeof( "/example/topic" );
    subscriptionCount = sizeof( subscriptionList ) / sizeof( IotMqttSubscription_t );
    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_SUBSCRIBE,
                                                &subscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Make sure buffer has enough space */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, bufferSize );

    /* Make sure subscription count of zero fails. */
    status = IotMqtt_SerializeSubscribe( &subscriptionList,
                                         0,
                                         remainingLength,
                                         &packetIdentifier,
                                         buffer,
                                         packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Make sure success is returned for good case. */
    status = IotMqtt_SerializeSubscribe( &subscriptionList,
                                         subscriptionCount,
                                         remainingLength,
                                         &packetIdentifier,
                                         buffer,
                                         packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

    /* For this example, IotMqtt_GetSubscriptionPacketSize() will return
     * packetSize = remainingLength +2 (two byte fixed header).
     * Make sure IotMqtt_SerializeSubscribe()
     * fails  when remaining length is more than packet size. */
    status = IotMqtt_SerializeSubscribe( &subscriptionList,
                                         subscriptionCount,
                                         remainingLength + 4,
                                         &packetIdentifier,
                                         buffer,
                                         packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_SerializeUnsubscribe works as intended.
 * to @ref mqtt_function_serializeunsubscribe.
 */
TEST( MQTT_Unit_API, SerializeUnsubscribeChecks )
{
    IotMqttSubscription_t subscriptionList;
    size_t subscriptionCount = 0;
    size_t remainingLength = 0;
    uint16_t packetIdentifier;
    uint8_t buffer[ 25 ];
    size_t bufferSize = sizeof( buffer );
    size_t packetSize = bufferSize;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    status = IotMqtt_SerializeUnsubscribe( NULL,
                                           subscriptionCount,
                                           remainingLength,
                                           &packetIdentifier,
                                           buffer,
                                           packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_SerializeUnsubscribe( &subscriptionList,
                                           subscriptionCount,
                                           remainingLength,
                                           NULL,
                                           buffer,
                                           packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_SerializeUnsubscribe( &subscriptionList,
                                           subscriptionCount,
                                           remainingLength,
                                           &packetIdentifier,
                                           NULL,
                                           packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Get correct values of packetsize and remaining length. */
    memset( ( void * ) &subscriptionList, 0x0, sizeof( subscriptionList ) );
    subscriptionList.qos = IOT_MQTT_QOS_0;
    subscriptionList.pTopicFilter = "/example/topic";
    subscriptionList.topicFilterLength = sizeof( "/example/topic" );
    subscriptionCount = sizeof( subscriptionList ) / sizeof( IotMqttSubscription_t );
    status = IotMqtt_GetSubscriptionPacketSize( IOT_MQTT_UNSUBSCRIBE,
                                                &subscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Make sure buffer has enough space */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, bufferSize );

    /* Make sure subscription count of zero fails. */
    status = IotMqtt_SerializeUnsubscribe( &subscriptionList,
                                           0,
                                           remainingLength,
                                           &packetIdentifier,
                                           buffer,
                                           packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Make sure success it returned for good case. */
    status = IotMqtt_SerializeUnsubscribe( &subscriptionList,
                                           subscriptionCount,
                                           remainingLength,
                                           &packetIdentifier,
                                           buffer,
                                           packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

    /* For this example, IotMqtt_GetSubscriptionPacketSize() will return
     * packetSize = remainingLength +2, make sure IotMqtt_SerializeUnsubscribe()
     * fails  when remaining length is more than packet size. */
    status = IotMqtt_SerializeUnsubscribe( &subscriptionList,
                                           subscriptionCount,
                                           remainingLength + 4,
                                           &packetIdentifier,
                                           buffer,
                                           packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_GetPublishPacketSize works as intended.
 * to @ref mqtt_function_getpublishpacketsize.
 */
TEST( MQTT_Unit_API, GetPublishPacketSizeChecks )
{
    IotMqttPublishInfo_t publishInfo;
    size_t remainingLength = 0;
    size_t packetSize;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Verify bad paramameters fail. */
    status = IotMqtt_GetPublishPacketSize( NULL, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetPublishPacketSize( &publishInfo, NULL, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_GetPublishPacketSize( &publishInfo, &remainingLength, NULL );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Empty topic must fail. */
    memset( ( void * ) &publishInfo, 0x00, sizeof( publishInfo ) );
    status = IotMqtt_GetPublishPacketSize( &publishInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Good case succeeds. */
    publishInfo.pTopicName = "/test/topic";
    publishInfo.topicNameLength = sizeof( "/test/topic" );
    status = IotMqtt_GetPublishPacketSize( &publishInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_GetPublishPacketSize works as intended.
 * to @ref mqtt_function_serializepublish.
 */
TEST( MQTT_Unit_API, SerializePublishChecks )
{
    IotMqttPublishInfo_t publishInfo;
    size_t remainingLength = 98;
    uint16_t packetIdentifier;
    uint8_t * pPacketIdentifierHigh;
    uint8_t buffer[ 100 ];
    size_t bufferSize = sizeof( buffer );
    size_t packetSize = bufferSize;
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Verify bad parameters fail. */
    memset( ( void * ) &publishInfo, 0x00, sizeof( publishInfo ) );
    publishInfo.pTopicName = "/test/topic";
    publishInfo.topicNameLength = sizeof( "/test/topic" );

    status = IotMqtt_SerializePublish( &publishInfo,
                                       remainingLength,
                                       NULL,
                                       &pPacketIdentifierHigh,
                                       buffer,
                                       packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_SerializePublish( NULL,
                                       remainingLength,
                                       &packetIdentifier,
                                       &pPacketIdentifierHigh,
                                       buffer,
                                       packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    status = IotMqtt_SerializePublish( &publishInfo,
                                       remainingLength,
                                       &packetIdentifier,
                                       &pPacketIdentifierHigh,
                                       NULL,
                                       packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* NULL topic fails. */
    publishInfo.pTopicName = NULL;
    status = IotMqtt_SerializePublish( &publishInfo,
                                       remainingLength,
                                       &packetIdentifier,
                                       &pPacketIdentifierHigh,
                                       buffer,
                                       packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Good case succeeds */
    publishInfo.pTopicName = "/test/topic";
    publishInfo.topicNameLength = sizeof( "/test/topic" );
    /* Calculate exact packet size and remaining length. */
    status = IotMqtt_GetPublishPacketSize( &publishInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Make sure buffer has enough space */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, bufferSize );

    status = IotMqtt_SerializePublish( &publishInfo,
                                       remainingLength,
                                       &packetIdentifier,
                                       &pPacketIdentifierHigh,
                                       buffer,
                                       packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_SerializeDisconnect works as intended.
 * to @ref mqtt_function_serializedisconnect.
 */
TEST( MQTT_Unit_API, SerializeDisconnectChecks )
{
    uint8_t buffer[ 10 ];
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Buffer size less than disconnect request fails. */
    status = IotMqtt_SerializeDisconnect( buffer, 1 );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* NULL buffer fails. */
    status = IotMqtt_SerializeDisconnect( NULL, 10 );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Good case succeeds. */
    status = IotMqtt_SerializeDisconnect( buffer, 2 );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_SerializePingReq works as intended.
 * to @ref mqtt_function_serializepingreq.
 */
TEST( MQTT_Unit_API, SerializePingReqChecks )
{
    uint8_t buffer[ 10 ];
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* Buffer size less than disconnect request fails. */
    status = IotMqtt_SerializePingreq( buffer, 1 );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* NULL buffer fails. */
    status = IotMqtt_SerializePingreq( NULL, 10 );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Good case succeeds. */
    status = IotMqtt_SerializePingreq( buffer, 2 );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_GetIncomingMQTTPacketTypeAndLength works as intended.
 * to @ref mqtt_function_getincomingmqttpackettypeandlength.
 */
TEST( MQTT_Unit_API, GetIncomingMQTTPacketTypeAndLengthChecks )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    IotMqttPacketInfo_t mqttPacket;
    uint8_t buffer[ 10 ];
    uint8_t * bufPtr = buffer;

    /* Dummy network interface - pointer to pointer to a buffer. */
    void * pNetworkInterface = ( void * ) &bufPtr;

    buffer[ 0 ] = 0x20; /* CONN ACK */
    buffer[ 1 ] = 0x02; /* Remaining length. */

    status = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &mqttPacket, _getNextByte, pNetworkInterface );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    TEST_ASSERT_EQUAL_INT( 0x20, mqttPacket.type );
    TEST_ASSERT_EQUAL_INT( 0x02, mqttPacket.remainingLength );

    /* Test with NULL network interface */
    status = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &mqttPacket, _getNextByte, NULL );
    TEST_ASSERT_EQUAL( IOT_MQTT_NETWORK_ERROR, status );

    /* Test with incorrect packet type. */
    buffer[ 0 ] = 0x10; /* INVALID */
    status = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &mqttPacket, _getNextByte, pNetworkInterface );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_RESPONSE, status );

    /* Test with invalid remaining length. */
    buffer[ 0 ] = 0x20; /* CONN ACK */
    /* To generate invalid remaining length response,
     * three bytes need to have MSB (or continuation bit, 0x80) set */
    buffer[ 1 ] = 0xFF;
    buffer[ 2 ] = 0xFF; 
    buffer[ 3 ] = 0xFF; 
    status = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &mqttPacket, _getNextByte, pNetworkInterface );
    TEST_ASSERT_EQUAL( IOT_MQTT_BAD_RESPONSE, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_DeserializeResponse works as intended.
 * to @ref mqtt_function_deserializeresponse.
 */
TEST( MQTT_Unit_API, DeserializeResponseChecks )
{
    IotMqttPacketInfo_t mqttPacketInfo;
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    uint8_t buffer[ 10 ];

    /* Verify parameters */
    status = IotMqtt_DeserializeResponse( NULL );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    memset( ( void * ) &mqttPacketInfo, 0x00, sizeof( mqttPacketInfo ) );

    mqttPacketInfo.type = 0x01;
    mqttPacketInfo.pRemainingData = buffer;
    status = IotMqtt_DeserializeResponse( &mqttPacketInfo );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    /* Good case succeeds - Test for CONN ACK */
    /* Set conn ack variable portion */
    buffer[ 0 ] = 0x00;
    buffer[ 1 ] = 0x00;
    /* Set type, remaining length and remaining data. */
    mqttPacketInfo.type = 0x20;            /* CONN ACK */
    mqttPacketInfo.pRemainingData = buffer;
    mqttPacketInfo.remainingLength = 0x02; /* CONN ACK Remaining Length. */
    status = IotMqtt_DeserializeResponse( &mqttPacketInfo );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that IotMqtt_DeserializePublish works as intended.
 * to @ref mqtt_function_deserializepublish.
 */
TEST( MQTT_Unit_API, DeserializePublishChecks )
{
    IotMqttPacketInfo_t mqttPacketInfo;
    IotMqttPublishInfo_t publishInfo;
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    uint8_t buffer[ 100 ];
    size_t bufferSize = sizeof( buffer );
    size_t packetSize = bufferSize;

    size_t remainingLength = 0;
    uint16_t packetIdentifier;
    uint8_t * pPacketIdentifierHigh;
    uint8_t * pNetworkInterface;

    /* Verify parameters. */
    status = IotMqtt_DeserializePublish( NULL );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );

    memset( ( void * ) &mqttPacketInfo, 0x00, sizeof( mqttPacketInfo ) );

    /* Bad Packet Type. */
    mqttPacketInfo.type = 0x01;
    mqttPacketInfo.pRemainingData = buffer;
    status = IotMqtt_DeserializePublish( &mqttPacketInfo );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_BAD_PARAMETER, status );


    /* Good case succeeds - Test for Publish. */
    /* 1. Find out length of the packet .*/
    memset( &publishInfo, 0x00, sizeof( publishInfo ) );
    publishInfo.pTopicName = "/test/topic";
    publishInfo.topicNameLength = ( uint16_t ) strlen( publishInfo.pTopicName );
    publishInfo.pPayload = "Hello World";
    publishInfo.payloadLength = ( uint16_t ) strlen( publishInfo.pPayload );
    publishInfo.qos = IOT_MQTT_QOS_0;
    /* Calculate exact packet size and remaining length */
    status = IotMqtt_GetPublishPacketSize( &publishInfo, &remainingLength, &packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Make sure buffer has enough space */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, bufferSize );

    /* 2. Serialize packet in the buffer. */
    status = IotMqtt_SerializePublish( &publishInfo,
                                       remainingLength,
                                       &packetIdentifier,
                                       &pPacketIdentifierHigh,
                                       buffer,
                                       packetSize );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );

    /* 3. Deserialize - get type and length. */
    pNetworkInterface = buffer;
    status = IotMqtt_GetIncomingMQTTPacketTypeAndLength( &mqttPacketInfo, _getNextByte, ( void * ) &pNetworkInterface );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
    /* Remaining data points to byte 3. */
    mqttPacketInfo.pRemainingData = &buffer[ 2 ];
    /* 4. Deserialize publish. */
    status = IotMqtt_DeserializePublish( &mqttPacketInfo );
    TEST_ASSERT_EQUAL_INT( IOT_MQTT_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests internal function  _mqttOperation_tryDestroy works
 * as intended.
 * @note: Uses access function.
 */
TEST( MQTT_Unit_API, MqttOperationTryDestroy )
{
    _mqttOperation_t * pMqttOperation = NULL;
    /* _mqttOperation_t mqttOperation ; */
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    IotTaskPoolJob_t pTaskPoolJob = IOT_TASKPOOL_JOB_INITIALIZER;
    IotTaskPoolError_t taskPoolError = IOT_TASKPOOL_SUCCESS;
    IotTaskPoolJobStorage_t _testJobStorage = IOT_TASKPOOL_JOB_STORAGE_INITIALIZER;

    /* Create Task pool Job */
    taskPoolError = IotTaskPool_CreateJob( _testTaskRoutine, NULL, &_testJobStorage, &pTaskPoolJob );
    TEST_ASSERT_EQUAL( IOT_TASKPOOL_SUCCESS, taskPoolError );
    /* Allocate operation */
    pMqttOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );
    TEST_ASSERT_NOT_NULL( pMqttOperation )
    /* Set up a mocked MQTT connection. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &mqttConnection ) );

    void * pData = ( void * ) pMqttOperation;
    memset( pData, 0, sizeof( _mqttOperation_t ) );

    /* Non Publish operation */
    pMqttOperation->incomingPublish = false;
    pMqttOperation->pMqttConnection = mqttConnection;
    pMqttOperation->job = pTaskPoolJob;
    pMqttOperation->u.operation.jobReference = 2;
    IotTestMqtt_mqttOperation_tryDestroy( pData );
    /* Job reference must be decremented, Operation must be still allocated */
    TEST_ASSERT_EQUAL_INT( 1, pMqttOperation->u.operation.jobReference );

    /* Publish Operation */
    /* reset mocked MQTT connection. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &mqttConnection ) );
    pMqttOperation->incomingPublish = true;
    pMqttOperation->u.publish.pReceivedData = IotMqtt_MallocMessage( 10 );

    /*
     * pOperation will be destroyed after this call and the test
     * should not report any memory leaks because the destroy
     * Operation should free all memory.
     */
    IotTestMqtt_mqttOperation_tryDestroy( pData );

    /* The call should not assert, operation should be destroyed */
    IotTest_MqttMockCleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests internal function  _createNetworkConnection works
 * as intended.
 * @note: Uses access function.
 */
TEST( MQTT_Unit_API, CreateNetworkConnectionCheck )
{
    IotMqttNetworkInfo_t * pNetworkInfo = NULL;
    IotNetworkConnection_t * pNetworkConnection = { 0 };
    bool createdNetworkConnection = false;

    /* Test for parameter validation */
    TEST_ASSERT_EQUAL( IOT_NETWORK_BAD_PARAMETER, IotTestMqtt_createNetworkConnection( pNetworkInfo,
                                                                                       pNetworkConnection,
                                                                                       &createdNetworkConnection ) );

    /* Setup correct network info */
    pNetworkInfo = &_networkInfo;
    pNetworkInfo->createNetworkConnection = true;
    pNetworkInfo->pNetworkInterface = &_networkInterface;
    _networkInterface.create = _createMock;
    /* Invalid server info */
    pNetworkInfo->u.setup.pNetworkServerInfo = NULL;

    TEST_ASSERT_NOT_EQUAL( IOT_MQTT_SUCCESS, IotTestMqtt_createNetworkConnection( pNetworkInfo,
                                                                                  pNetworkConnection,
                                                                                  &createdNetworkConnection ) );
}

/*-----------------------------------------------------------*/
