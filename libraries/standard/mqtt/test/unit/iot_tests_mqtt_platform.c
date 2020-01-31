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
 * @file iot_tests_mqtt_platform.c
 * @brief Tests interaction of MQTT with the lower layers, such as network and task pool.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* MQTT test access include. */
#include "iot_test_access_mqtt.h"

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

/*-----------------------------------------------------------*/

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
    RUN_TEST_CASE( MQTT_Unit_Platform, ConnectNetworkFailures );
    RUN_TEST_CASE( MQTT_Unit_Platform, ConnectScheduleFailures );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref mqtt_function_connect when the network fails.
 */
TEST( MQTT_Unit_Platform, ConnectNetworkFailures )
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
TEST( MQTT_Unit_Platform, ConnectScheduleFailures )
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
}

/*-----------------------------------------------------------*/
