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

/* JSON utilities include. */
#include "iot_json_utils.h"

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

/**
 * @brief Job IDs retrieved from the AWS IoT Jobs service.
 */
static char _pJobIds[ 2 ][ JOBS_MAX_ID_LENGTH + 1 ] = { { 0 } };

/**
 * @brief Lengths of the Job IDs retrieved from the AWS IoT Jobs service.
 */
static size_t _pJobIdLengths[ 2 ] = { 0 };

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
 * @brief Parses Job IDs from a GET PENDING Jobs response.
 */
static void _parseJobIds( const AwsIotJobsResponse_t * pJobsResponse )
{
    bool status = true;
    int32_t i = 0;
    const char * pInProgressJobs = NULL, * pParseStart = NULL, * pJobId = NULL;
    size_t inProgressJobsLength = 0, parseLength = 0, jobIdLength = 0;

    /* In-progress Jobs for this device will interfere with the tests; fail if
     * any in-progress Jobs are present. */
    status = IotJsonUtils_FindJsonValue( pJobsResponse->pJobsResponse,
                                         pJobsResponse->jobsResponseLength,
                                         "inProgressJobs", 14,
                                         &pInProgressJobs,
                                         &inProgressJobsLength );
    TEST_ASSERT_EQUAL_INT( true, status );
    TEST_ASSERT_NOT_NULL( pInProgressJobs );
    TEST_ASSERT_EQUAL_MESSAGE( 2, inProgressJobsLength, "In-progress Jobs detected. Tests will not run." );

    /* Parse for the list of queued Jobs. This is where parsing for Job IDs will
     * start. */
    status = IotJsonUtils_FindJsonValue( pJobsResponse->pJobsResponse,
                                         pJobsResponse->jobsResponseLength,
                                         "queuedJobs",
                                         10,
                                         &pParseStart,
                                         &parseLength );
    TEST_ASSERT_EQUAL_INT_MESSAGE( true, status, "Response did not contain any queued Jobs." );
    TEST_ASSERT_NOT_NULL( pParseStart );
    TEST_ASSERT_GREATER_THAN( 0, parseLength );

    /* Parse the Job IDs of the first two queued Jobs. */
    for( i = 0; i < 2; i++ )
    {
        status = IotJsonUtils_FindJsonValue( pParseStart,
                                             parseLength,
                                             "jobId",
                                             5,
                                             &pJobId,
                                             &jobIdLength );
        TEST_ASSERT_EQUAL_INT_MESSAGE( true, status, "Response did not contain enough queued Jobs." );
        TEST_ASSERT_NOT_NULL( pJobId );
        TEST_ASSERT_GREATER_THAN( 0, jobIdLength );
        TEST_ASSERT_LESS_THAN_MESSAGE( JOBS_MAX_ID_LENGTH,
                                       jobIdLength - 2,
                                       "Response contains a Job ID that is too long." );

        /* Job ID must start and end with quotes, as it is a string. */
        TEST_ASSERT_EQUAL( '"', *pJobId );
        TEST_ASSERT_EQUAL( '"', *( pJobId + jobIdLength - 1 ) );

        /* Copy the Job ID, excluding the quotes. Save its length too. */
        ( void ) memcpy( _pJobIds[ i ], pJobId + 1, jobIdLength - 2 );
        _pJobIdLengths[ i ] = jobIdLength - 2;

        /* To find the next Job ID, it's sufficient to search again after the current one. */
        parseLength -= ( pJobId - pParseStart );
        pParseStart = pJobId;
    }
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
                status = AwsIotJobs_Describe( &requestInfo,
                                              AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
                                              true,
                                              0,
                                              &callbackInfo,
                                              &( callbackParam.operation ) );
                break;

            default:
                /* The only remaining valid type is UPDATE. */
                TEST_ASSERT_EQUAL( JOBS_UPDATE, type );

                /* Set a Job ID that doesn't exist. */
                requestInfo.pJobId = _pJobIds[ 0 ];
                requestInfo.jobIdLength = _pJobIdLengths[ 0 ];

                status = AwsIotJobs_Update( &requestInfo,
                                            &updateInfo,
                                            0,
                                            &callbackInfo,
                                            &( callbackParam.operation ) );
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
    const char * pJobId = NULL;
    size_t jobIdLength = 0;

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
            status = AwsIotJobs_TimedDescribe( &requestInfo,
                                               AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
                                               true,
                                               0,
                                               AWS_IOT_TEST_JOBS_TIMEOUT,
                                               &jobsResponse );
            break;

        default:
            /* The only remaining valid type is UPDATE. */
            TEST_ASSERT_EQUAL( JOBS_UPDATE, type );

            requestInfo.pJobId = _pJobIds[ 0 ];
            requestInfo.jobIdLength = _pJobIdLengths[ 0 ];

            status = AwsIotJobs_TimedUpdate( &requestInfo,
                                             &updateInfo,
                                             0,
                                             AWS_IOT_TEST_JOBS_TIMEOUT,
                                             &jobsResponse );
            break;
    }

    TEST_ASSERT_EQUAL( expectedResult, status );

    /* Check the Jobs response. */
    TEST_ASSERT_NOT_NULL( jobsResponse.pJobsResponse );
    TEST_ASSERT_GREATER_THAN( 0, jobsResponse.jobsResponseLength );

    /* Save the list of queued Jobs. */
    if( type == JOBS_GET_PENDING )
    {
        _parseJobIds( &jobsResponse );

        /* Job IDs must be unique; check that the parsed IDs are different. */
        if( _pJobIdLengths[ 0 ] == _pJobIdLengths[ 1 ] )
        {
            TEST_ASSERT_NOT_EQUAL( 0, strncmp( _pJobIds[ 0 ],
                                               _pJobIds[ 1 ],
                                               _pJobIdLengths[ 0 ] ) );
        }
    }
    else
    {
        /* Check that the Job ID matches the first queued Job. The Jobs service
         * provides an ordering guarantee. Don't check for UPDATE; its response
         * does not include the Job ID. */
        if( type != JOBS_UPDATE )
        {
            TEST_ASSERT_EQUAL_INT( true, IotJsonUtils_FindJsonValue( jobsResponse.pJobsResponse,
                                                                     jobsResponse.jobsResponseLength,
                                                                     "jobId",
                                                                     5,
                                                                     &pJobId,
                                                                     &jobIdLength ) );
            TEST_ASSERT_EQUAL( _pJobIdLengths[ 0 ], jobIdLength - 2 );
            TEST_ASSERT_EQUAL_STRING_LEN( _pJobIds[ 0 ], pJobId + 1, _pJobIdLengths[ 0 ] );
        }
    }

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
    /* The tests for Get Pending must run first, as they retrieve the list of
     * Jobs for the other tests. */
    RUN_TEST_CASE( Jobs_System, GetPendingAsync );
    RUN_TEST_CASE( Jobs_System, GetPendingBlocking );

    /* Only run the following tests if 2 queued Jobs are available. */
    if( ( _pJobIdLengths[ 0 ] > 0 ) && ( _pJobIdLengths[ 1 ] > 0 ) )
    {
        RUN_TEST_CASE( Jobs_System, StartNextAsync );
        RUN_TEST_CASE( Jobs_System, StartNextBlocking );
        RUN_TEST_CASE( Jobs_System, DescribeAsync );
        RUN_TEST_CASE( Jobs_System, DescribeBlocking );
        RUN_TEST_CASE( Jobs_System, UpdateAsync );
        RUN_TEST_CASE( Jobs_System, UpdateBlocking );
    }

    RUN_TEST_CASE( Jobs_System, PersistentSubscriptions );
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
 * @brief Starts the next Job using @ref jobs_function_startnext.
 */
TEST( Jobs_System, StartNextAsync )
{
    _jobsAsyncTest( JOBS_START_NEXT, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Starts the next Job using @ref jobs_function_timedstartnext.
 */
TEST( Jobs_System, StartNextBlocking )
{
    _jobsBlockingTest( JOBS_START_NEXT, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Describe a Job using @ref jobs_function_describe.
 */
TEST( Jobs_System, DescribeAsync )
{
    _jobsAsyncTest( JOBS_DESCRIBE, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Describe a Job using @ref jobs_function_timeddescribe.
 */
TEST( Jobs_System, DescribeBlocking )
{
    _jobsBlockingTest( JOBS_DESCRIBE, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Update a Job status using @ref jobs_function_update.
 */
TEST( Jobs_System, UpdateAsync )
{
    _jobsAsyncTest( JOBS_UPDATE, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Update a Job status using @ref jobs_function_timedupdate.
 */
TEST( Jobs_System, UpdateBlocking )
{
    _jobsBlockingTest( JOBS_UPDATE, AWS_IOT_JOBS_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests a Job operation with perisistent subscriptions.
 */
TEST( Jobs_System, PersistentSubscriptions )
{
    uint64_t startTime = 0, elapsedTime1 = 0, elapsedTime2 = 0;
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsResponse_t response = AWS_IOT_JOBS_RESPONSE_INITIALIZER;

    /* Set the Jobs request parameters. */
    requestInfo.mqttConnection = _mqttConnection;
    requestInfo.pThingName = AWS_IOT_TEST_JOBS_THING_NAME;
    requestInfo.thingNameLength = ( sizeof( AWS_IOT_TEST_JOBS_THING_NAME ) - 1 );
    requestInfo.mallocResponse = IotTest_Malloc;

    /* Time a Jobs function that sets persistent subscriptions. */
    startTime = IotClock_GetTimeMs();
    status = AwsIotJobs_TimedGetPending( &requestInfo,
                                         AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS,
                                         AWS_IOT_TEST_JOBS_TIMEOUT,
                                         &response );
    elapsedTime1 = IotClock_GetTimeMs() - startTime;

    /* Check results. */
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );
    TEST_ASSERT_NOT_NULL( response.pJobsResponse );
    TEST_ASSERT_GREATER_THAN( 0, response.jobsResponseLength );

    IotTest_Free( ( void * ) response.pJobsResponse );

    /* Time a Jobs functions that has persistent subscriptions set. */
    startTime = IotClock_GetTimeMs();
    status = AwsIotJobs_TimedGetPending( &requestInfo,
                                         0,
                                         AWS_IOT_TEST_JOBS_TIMEOUT,
                                         &response );
    elapsedTime2 = IotClock_GetTimeMs() - startTime;

    /* Check results */
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );
    TEST_ASSERT_NOT_NULL( response.pJobsResponse );
    TEST_ASSERT_GREATER_THAN( 0, response.jobsResponseLength );

    IotTest_Free( ( void * ) response.pJobsResponse );

    /* Becuase the second operation has persistent subscriptions and does not
     * need to subscribe to anything, it should be significantly faster. */
    TEST_ASSERT_LESS_THAN( elapsedTime1, elapsedTime2 );

    /* Remove persistent subscriptions. */
    status = AwsIotJobs_RemovePersistentSubscriptions( &requestInfo,
                                                       AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );
}

/*-----------------------------------------------------------*/
