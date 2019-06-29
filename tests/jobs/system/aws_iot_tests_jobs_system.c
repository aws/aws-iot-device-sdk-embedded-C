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
 * @file aws_iot_tests_jobs_system.c
 * @brief Full system tests for the AWS IoT Jobs library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Jobs include. */
#include "private/aws_iot_jobs_internal.h"

/* Test network header include. */
#include IOT_TEST_NETWORK_HEADER

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values of test configuration constants.
 */
#ifndef IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S
    #define IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S    ( 30 )
#endif
#ifndef AWS_IOT_TEST_JOBS_TIMEOUT
    #define AWS_IOT_TEST_JOBS_TIMEOUT                   ( 5000 )
#endif
/** @endcond */

/* Thing Name must be defined for these tests. */
#ifndef AWS_IOT_TEST_JOBS_THING_NAME
    #error "Please define AWS_IOT_TEST_JOBS_THING_NAME."
#endif

/* Require Jobs library asserts to be enabled for these tests. The Jobs
 * assert function is used to abort the tests on failure from the Jobs operation
 * complete callback. */
#if AWS_IOT_JOBS_ENABLE_ASSERTS == 0
    #error "Jobs system tests require AWS_IOT_JOBS_ENABLE_ASSERTS to be 1."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Parameter 1 of #_operationComplete.
 */
typedef struct _operationCompleteParams
{
    AwsIotJobsCallbackType_t expectedType; /**< @brief Expected callback type. */
    AwsIotJobsError_t expectedResult;      /**< @brief Expected operation result. */
    IotSemaphore_t waitSem;                /**< @brief Used to unblock waiting test thread. */
    AwsIotJobsOperation_t operation;       /**< @brief Reference to expected completed operation. */
} _operationCompleteParams_t;

/*-----------------------------------------------------------*/

/**
 * @brief Network server info to share among the tests.
 */
static const IotTestNetworkServerInfo_t _serverInfo = IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER;

/**
 * @brief Network credential info to share among the tests.
 */
#if IOT_TEST_SECURED_CONNECTION == 1
    static const IotTestNetworkCredentials_t _credentials = IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER;
#endif

/**
 * @brief An MQTT network setup parameter to share among the tests.
 */
static IotMqttNetworkInfo_t _networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief An MQTT connection to share among the tests.
 */
static IotMqttConnection_t _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/*-----------------------------------------------------------*/

/**
 * @brief Jobs operation completion callback function. Checks parameters
 * and unblocks the main test thread.
 */
static void _operationComplete( void * pArgument,
                                AwsIotJobsCallbackParam_t * pOperation )
{
    _operationCompleteParams_t * pParams = ( _operationCompleteParams_t * ) pArgument;

    /* Check parameters against expected values. */
    AwsIotJobs_Assert( pParams->expectedType == pOperation->callbackType );
    AwsIotJobs_Assert( pParams->operation == pOperation->u.operation.reference );
    AwsIotJobs_Assert( pParams->expectedResult == pOperation->u.operation.result );

    AwsIotJobs_Assert( pOperation->mqttConnection == _mqttConnection );
    AwsIotJobs_Assert( pOperation->thingNameLength == sizeof( AWS_IOT_TEST_JOBS_THING_NAME ) - 1 );
    AwsIotJobs_Assert( strncmp( pOperation->pThingName,
                                AWS_IOT_TEST_JOBS_THING_NAME,
                                pOperation->thingNameLength ) == 0 );

    AwsIotJobs_Assert( pOperation->u.operation.pResponse != NULL );
    AwsIotJobs_Assert( pOperation->u.operation.responseLength > 0 );

    /* Unblock the main test thead. */
    IotSemaphore_Post( &( pParams->waitSem ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Common code of the Jobs Async tests.
 */
static void _jobsAsyncTest( _jobsOperationType_t type,
                            AwsIotJobsError_t expectedResult )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    _operationCompleteParams_t callbackParam = { .expectedType = ( AwsIotJobsCallbackType_t ) 0 };

    /* Initialize the wait semaphore. */
    TEST_ASSERT_EQUAL_INT( true, IotSemaphore_Create( &( callbackParam.waitSem ), 0, 1 ) );

    if( TEST_PROTECT() )
    {
        /* Set the callback information. */
        callbackParam.expectedType = ( AwsIotJobsCallbackType_t ) type;
        callbackParam.expectedResult = expectedResult;
        callbackInfo.function = _operationComplete;
        callbackInfo.pCallbackContext = &callbackParam;

        /* Set the Jobs request parameters. */
        requestInfo.mqttConnection = _mqttConnection;
        requestInfo.pThingName = AWS_IOT_TEST_JOBS_THING_NAME;
        requestInfo.thingNameLength = ( sizeof( AWS_IOT_TEST_JOBS_THING_NAME ) - 1 );
        requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
        requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

        /* Call Jobs function. */
        switch( type )
        {
            case JOBS_GET_PENDING:
                status = AwsIotJobs_GetPending( &requestInfo,
                                                0,
                                                &callbackInfo,
                                                &( callbackParam.operation ) );
                break;

            case JOBS_START_NEXT:
                status = AwsIotJobs_StartNext( &requestInfo,
                                               &updateInfo,
                                               0,
                                               &callbackInfo,
                                               &( callbackParam.operation ) );
                break;

            case JOBS_DESCRIBE:
                break;

            default:
                /* The only remaining valid type is UPDATE. */
                TEST_ASSERT_EQUAL( JOBS_UPDATE, type );
                break;
        }

        TEST_ASSERT_EQUAL( AWS_IOT_JOBS_STATUS_PENDING, status );

        if( IotSemaphore_TimedWait( &( callbackParam.waitSem ),
                                    AWS_IOT_TEST_JOBS_TIMEOUT ) == false )
        {
            TEST_FAIL_MESSAGE( "Timed out waiting for pending Jobs." );
        }
    }

    IotSemaphore_Destroy( &( callbackParam.waitSem ) );
}

/*-----------------------------------------------------------*/

static void _jobsBlockingTest( _jobsOperationType_t type,
                               AwsIotJobsError_t expectedResult )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsResponse_t jobsResponse = AWS_IOT_JOBS_RESPONSE_INITIALIZER;

    /* Set the Jobs request parameters. */
    requestInfo.mqttConnection = _mqttConnection;
    requestInfo.pThingName = AWS_IOT_TEST_JOBS_THING_NAME;
    requestInfo.thingNameLength = ( sizeof( AWS_IOT_TEST_JOBS_THING_NAME ) - 1 );
    requestInfo.mallocResponse = IotTest_Malloc;
    requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
    requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

    /* Call Jobs function. */
    switch( type )
    {
        case JOBS_GET_PENDING:
            status = AwsIotJobs_TimedGetPending( &requestInfo,
                                                 0,
                                                 AWS_IOT_TEST_JOBS_TIMEOUT,
                                                 &jobsResponse );
            break;

        case JOBS_START_NEXT:
            status = AwsIotJobs_TimedStartNext( &requestInfo,
                                                &updateInfo,
                                                0,
                                                AWS_IOT_TEST_JOBS_TIMEOUT,
                                                &jobsResponse );
            break;

        case JOBS_DESCRIBE:
            break;

        default:
            /* The only remaining valid type is UPDATE. */
            TEST_ASSERT_EQUAL( JOBS_UPDATE, type );
            break;
    }

    TEST_ASSERT_EQUAL( expectedResult, status );

    /* Check the Jobs response. */
    TEST_ASSERT_NOT_NULL( jobsResponse.pJobsResponse );
    TEST_ASSERT_GREATER_THAN( 0, jobsResponse.jobsResponseLength );

    /* Free the allocated Jobs response. */
    IotTest_Free( ( void * ) jobsResponse.pJobsResponse );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Jobs system tests.
 */
TEST_GROUP( Jobs_System );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Jobs system tests.
 */
TEST_SETUP( Jobs_System )
{
    static uint64_t lastConnectTime = 0;
    uint64_t elapsedTime = 0;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    /* Initialize SDK. */
    if( IotSdk_Init() == false )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize SDK." );
    }

    /* Set up the network stack. */
    if( IotTestNetwork_Init() != IOT_NETWORK_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to set up network stack." );
    }

    /* Initialize the MQTT library. */
    if( IotMqtt_Init() != IOT_MQTT_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize MQTT library." );
    }

    /* Initialize the Jobs library. */
    if( AwsIotJobs_Init( 0 ) != AWS_IOT_JOBS_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize Jobs library." );
    }

    /* Set the MQTT network setup parameters. */
    ( void ) memset( &_networkInfo, 0x00, sizeof( IotMqttNetworkInfo_t ) );
    _networkInfo.createNetworkConnection = true;
    _networkInfo.u.setup.pNetworkServerInfo = ( void * ) &_serverInfo;
    _networkInfo.pNetworkInterface = IOT_TEST_NETWORK_INTERFACE;

    #if IOT_TEST_SECURED_CONNECTION == 1
        _networkInfo.u.setup.pNetworkCredentialInfo = ( void * ) &_credentials;
    #endif

    #ifdef IOT_TEST_MQTT_SERIALIZER
        _networkInfo.pMqttSerializer = IOT_TEST_MQTT_SERIALIZER;
    #endif

    /* Set the members of the connect info. Use the Jobs Thing Name as the MQTT
     * client identifier. */
    connectInfo.awsIotMqttMode = true;
    connectInfo.pClientIdentifier = AWS_IOT_TEST_JOBS_THING_NAME;
    connectInfo.clientIdentifierLength = ( uint16_t ) ( sizeof( AWS_IOT_TEST_JOBS_THING_NAME ) - 1 );
    connectInfo.keepAliveSeconds = IOT_TEST_MQTT_SHORT_KEEPALIVE_INTERVAL_S;

    /* AWS IoT Service limits only allow 1 connection per MQTT client ID per second.
     * Wait until 1100 ms have elapsed since the last connection. */
    elapsedTime = IotClock_GetTimeMs() - lastConnectTime;

    if( elapsedTime < 1100ULL )
    {
        IotClock_SleepMs( 1100UL - ( uint32_t ) elapsedTime );
    }

    /* Establish an MQTT connection. */
    if( IotMqtt_Connect( &_networkInfo,
                         &connectInfo,
                         AWS_IOT_TEST_JOBS_TIMEOUT,
                         &_mqttConnection ) != IOT_MQTT_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to establish MQTT connection for Jobs tests." );
    }

    /* Update the time of the last MQTT connect. */
    lastConnectTime = IotClock_GetTimeMs();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Jobs system tests.
 */
TEST_TEAR_DOWN( Jobs_System )
{
    /* Disconnect the MQTT connection if it was created. */
    if( _mqttConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotMqtt_Disconnect( _mqttConnection, 0 );
        _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    }

    /* Clean up the Jobs library. */
    AwsIotJobs_Cleanup();

    /* Clean up the MQTT library. */
    IotMqtt_Cleanup();

    /* Clean up the network stack. */
    IotTestNetwork_Cleanup();

    /* Clean up SDK. */
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Jobs system tests.
 */
TEST_GROUP_RUNNER( Jobs_System )
{
    RUN_TEST_CASE( Jobs_System, GetPendingAsync );
    RUN_TEST_CASE( Jobs_System, GetPendingBlocking );
    RUN_TEST_CASE( Jobs_System, StartNextAsync );
    RUN_TEST_CASE( Jobs_System, StartNextBlocking );
}

/*-----------------------------------------------------------*/

/**
 * @brief Retrieves a list of Jobs using @ref jobs_function_timedgetpending.
 */
TEST( Jobs_System, GetPendingAsync )
{
    _jobsAsyncTest( JOBS_GET_PENDING, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Retrieves a list of Jobs using @ref jobs_function_timedgetpending.
 */
TEST( Jobs_System, GetPendingBlocking )
{
    _jobsBlockingTest( JOBS_GET_PENDING, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Starts the next jobs using @ref jobs_function_startnext.
 */
TEST( Jobs_System, StartNextAsync )
{
    _jobsAsyncTest( JOBS_START_NEXT, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Starts the next jobs using @ref jobs_function_timedstartnext.
 */
TEST( Jobs_System, StartNextBlocking )
{
    _jobsBlockingTest( JOBS_START_NEXT, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/
