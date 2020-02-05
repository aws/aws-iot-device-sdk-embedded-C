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

/* Allow these tests to manipulate the task pool and create failures by including
 * the task pool internal header. */
#undef LIBRARY_LOG_LEVEL
#undef LIBRARY_LOG_NAME
#include "../src/private/iot_taskpool_internal.h"

/* MQTT test access include. */
#include "iot_test_access_mqtt.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

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

/*-----------------------------------------------------------*/

/**
 * @brief An #IotMqttNetworkInfo_t to share among the tests.
 */
static IotMqttNetworkInfo_t _networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief An #IotNetworkInterface_t to share among the tests.
 */
static IotNetworkInterface_t _networkInterface = { 0 };

/*
 * Return values of the mocked network functions.
 */
static IotNetworkError_t _createStatus = IOT_NETWORK_SUCCESS;             /**< @brief Return value for #_networkCreate. */
static IotNetworkError_t _setReceiveCallbackStatus = IOT_NETWORK_SUCCESS; /**< @brief Return value for #_networkSetReceiveCallback. */
static IotNetworkError_t _sendStatus = IOT_NETWORK_SUCCESS;               /**< @brief Return value for #_networkSend. */
static IotNetworkError_t _closeStatus = IOT_NETWORK_SUCCESS;              /**< @brief Return value for #_networkClose. */
static IotNetworkError_t _destroyStatus = IOT_NETWORK_SUCCESS;            /**< @brief Return value for #_networkDestroy. */

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
 * @brief Test group for MQTT platform tests.
 */
TEST_GROUP( MQTT_Unit_Platform );

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
 * @brief Test tear down for MQTT platform tests.
 */
TEST_TEAR_DOWN( MQTT_Unit_Platform )
{
    IotMqtt_Cleanup();
    IotSdk_Cleanup();
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
