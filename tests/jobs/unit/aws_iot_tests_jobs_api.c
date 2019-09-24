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
 * @file aws_iot_tests_jobs_api.c
 * @brief Tests for the user-facing API functions (declared in aws_iot_jobs.h).
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

/* Test framework includes. */
#include "unity_fixture.h"

/**
 * @brief Whether to check the number of MQTT library errors in the malloc
 * failure tests.
 *
 * Should only be checked if malloc overrides are available and not testing for
 * code coverage. In static memory mode, there should be no MQTT library errors.
 */
#if ( IOT_TEST_COVERAGE == 1 ) || ( IOT_TEST_NO_MALLOC_OVERRIDES == 1 )
    #define CHECK_MQTT_ERROR_COUNT( expected, actual )
#else
    #if ( IOT_STATIC_MEMORY_ONLY == 1 )
        #define CHECK_MQTT_ERROR_COUNT( expected, actual )    TEST_ASSERT_EQUAL( 0, actual )
    #else
        #define CHECK_MQTT_ERROR_COUNT( expected, actual )    TEST_ASSERT_EQUAL( expected, actual )
    #endif
#endif

/*-----------------------------------------------------------*/

/**
 * @brief The Thing Name shared among all the tests.
 */
#define TEST_THING_NAME             "TestThingName"

/**
 * @brief The length of #TEST_THING_NAME.
 */
#define TEST_THING_NAME_LENGTH      ( sizeof( TEST_THING_NAME ) - 1 )

/**
 * @brief A non-NULL callback function that can be tested by Jobs, but is not
 * expected to be invoked.
 */
#define JOBS_CALLBACK_FUNCTION      ( ( void ( * )( void *, AwsIotJobsCallbackParam_t * ) ) 0x01 )

/**
 * @brief Another non-NULL callback function that can be tested by Jobs, but is not
 * expected to be invoked.
 */
#define JOBS_CALLBACK_FUNCTION_2    ( ( void ( * )( void *, AwsIotJobsCallbackParam_t * ) ) 0x02 )

/*-----------------------------------------------------------*/

/**
 * @brief The MQTT connection shared among the tests.
 */
static IotMqttConnection_t _pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/*-----------------------------------------------------------*/

/**
 * @brief Common code of the MallocFail tests.
 */
static void _jobsMallocFail( _jobsOperationType_t type )
{
    int32_t i = 0, mqttErrorCount = 0;
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsOperation_t operation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsResponse_t jobsResponse = AWS_IOT_JOBS_RESPONSE_INITIALIZER;

    /* Set a short timeout so this test runs faster. */
    _AwsIotJobsMqttTimeoutMs = 75;

    /* Set the members of the request info. */
    requestInfo.mqttConnection = _pMqttConnection;
    requestInfo.pThingName = TEST_THING_NAME;
    requestInfo.thingNameLength = TEST_THING_NAME_LENGTH;
    requestInfo.mallocResponse = IotTest_Malloc;
    requestInfo.pJobId = "jobid";
    requestInfo.jobIdLength = 5;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call Jobs operation. Memory allocation will fail at various times
         * during this call. */
        switch( type )
        {
            case JOBS_GET_PENDING:
                status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                                     AWS_IOT_JOBS_FLAG_WAITABLE,
                                                     NULL,
                                                     &operation );
                break;

            case JOBS_START_NEXT:
                status = AwsIotJobs_StartNextAsync( &requestInfo,
                                                    &updateInfo,
                                                    AWS_IOT_JOBS_FLAG_WAITABLE,
                                                    NULL,
                                                    &operation );
                break;

            case JOBS_DESCRIBE:
                status = AwsIotJobs_DescribeAsync( &requestInfo,
                                                   AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
                                                   false,
                                                   AWS_IOT_JOBS_FLAG_WAITABLE,
                                                   NULL,
                                                   &operation );
                break;

            default:
                /* The only remaining valid type is update. */
                TEST_ASSERT_EQUAL( JOBS_UPDATE, type );

                status = AwsIotJobs_UpdateAsync( &requestInfo,
                                                 &updateInfo,
                                                 AWS_IOT_JOBS_FLAG_WAITABLE,
                                                 NULL,
                                                 &operation );
                break;
        }

        /* Once the Jobs operation call succeeds, wait for it to complete. */
        if( status == AWS_IOT_JOBS_STATUS_PENDING )
        {
            /* No response will be received from the network, so the Jobs operation
             * is expected to time out. */
            TEST_ASSERT_EQUAL( AWS_IOT_JOBS_TIMEOUT,
                               AwsIotJobs_Wait( operation,
                                                0,
                                                &jobsResponse ) );
            break;
        }

        /* Count the number of MQTT library errors. Otherwise, check that the error
         * is a "No memory" error. */
        if( status == AWS_IOT_JOBS_MQTT_ERROR )
        {
            mqttErrorCount++;
        }
        else
        {
            TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NO_MEMORY, status );
        }
    }

    /* Allow 3 MQTT library errors, which are caused by failure to allocate memory
     * for incoming packets (SUBSCRIBE, PUBLISH). */
    CHECK_MQTT_ERROR_COUNT( 2, mqttErrorCount );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Jobs API tests.
 */
TEST_GROUP( Jobs_Unit_API );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Jobs API tests.
 */
TEST_SETUP( Jobs_Unit_API )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the MQTT library. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );

    /* Initialize the Jobs library. */
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, AwsIotJobs_Init( 0 ) );

    /* Initialize MQTT mock. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &_pMqttConnection ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Jobs API tests.
 */
TEST_TEAR_DOWN( Jobs_Unit_API )
{
    /* Clean up MQTT mock. */
    IotTest_MqttMockCleanup();

    /* Clean up libraries. */
    AwsIotJobs_Cleanup();
    IotMqtt_Cleanup();
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Jobs API tests.
 */
TEST_GROUP_RUNNER( Jobs_Unit_API )
{
    RUN_TEST_CASE( Jobs_Unit_API, Init );
    RUN_TEST_CASE( Jobs_Unit_API, StringCoverage );
    RUN_TEST_CASE( Jobs_Unit_API, OperationInvalidRequestInfo );
    RUN_TEST_CASE( Jobs_Unit_API, OperationInvalidUpdateInfo );
    RUN_TEST_CASE( Jobs_Unit_API, WaitInvalidParameters );
    RUN_TEST_CASE( Jobs_Unit_API, GetPendingMallocFail );
    RUN_TEST_CASE( Jobs_Unit_API, StartNextMallocFail );
    RUN_TEST_CASE( Jobs_Unit_API, DescribeMallocFail );
    RUN_TEST_CASE( Jobs_Unit_API, UpdateMallocFail );
    RUN_TEST_CASE( Jobs_Unit_API, RemovePersistentSubscriptions );
    RUN_TEST_CASE( Jobs_Unit_API, SetCallback );
    RUN_TEST_CASE( Jobs_Unit_API, SetCallbackMallocFail );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the function @ref jobs_function_init.
 */
TEST( Jobs_Unit_API, Init )
{
    int32_t i = 0;
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsOperation_t operation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    AwsIotJobsResponse_t response = AWS_IOT_JOBS_RESPONSE_INITIALIZER;

    /* Check that test set up set the default value. */
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotJobsMqttTimeoutMs );

    /* The Jobs library was already initialized by test set up. Clean it up
     * before running this test. */
    AwsIotJobs_Cleanup();

    /* Calling cleanup twice should not crash. */
    AwsIotJobs_Cleanup();

    /* Set a MQTT timeout. */
    AwsIotJobs_Init( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS + 1 );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS + 1, _AwsIotJobsMqttTimeoutMs );

    /* Cleanup should restore the default MQTT timeout. */
    AwsIotJobs_Cleanup();
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotJobsMqttTimeoutMs );

    /* Calling API functions without calling AwsIotJobs_Init should fail. */
    requestInfo.mqttConnection = _pMqttConnection;
    requestInfo.pThingName = TEST_THING_NAME;
    requestInfo.thingNameLength = TEST_THING_NAME_LENGTH;
    status = AwsIotJobs_GetPendingAsync( &requestInfo, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    status = AwsIotJobs_StartNextAsync( &requestInfo, &updateInfo, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    status = AwsIotJobs_DescribeAsync( &requestInfo, AWS_IOT_JOBS_NO_EXECUTION_NUMBER, false, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    status = AwsIotJobs_UpdateAsync( &requestInfo, &updateInfo, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    status = AwsIotJobs_Wait( operation, 500, &response );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    status = AwsIotJobs_SetNotifyPendingCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NOT_INITIALIZED, status );

    /* Test Jobs initialization with mutex creation failures. */
    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        status = AwsIotJobs_Init( 0 );

        /* Check that the status is either success or "INIT FAILED". */
        if( status == AWS_IOT_JOBS_SUCCESS )
        {
            break;
        }

        TEST_ASSERT_EQUAL( AWS_IOT_JOBS_INIT_FAILED, status );
    }

    /* Initialize the Jobs library for test clean up. Calling init twice should not crash. */
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, AwsIotJobs_Init( 0 ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Provides code coverage of the Jobs enum-to-string functions,
 * @ref jobs_function_strerror and @ref jobs_function_statename.
 */
TEST( Jobs_Unit_API, StringCoverage )
{
    size_t i = 0;
    const char * pMessage = NULL;

    const char * pInvalidStatus = "INVALID STATUS";
    size_t invalidStatusLength = strlen( pInvalidStatus );

    /* For each Jobs Error, check the returned string. */
    const AwsIotJobsError_t pApiErrors[] =
    {
        AWS_IOT_JOBS_SUCCESS,        AWS_IOT_JOBS_STATUS_PENDING, AWS_IOT_JOBS_INIT_FAILED,
        AWS_IOT_JOBS_BAD_PARAMETER,  AWS_IOT_JOBS_NO_MEMORY,      AWS_IOT_JOBS_MQTT_ERROR,
        AWS_IOT_JOBS_BAD_RESPONSE,   AWS_IOT_JOBS_TIMEOUT,        AWS_IOT_JOBS_NOT_INITIALIZED,
        AWS_IOT_JOBS_INVALID_TOPIC,  AWS_IOT_JOBS_INVALID_JSON,   AWS_IOT_JOBS_INVALID_REQUEST,
        AWS_IOT_JOBS_INVALID_STATE,  AWS_IOT_JOBS_NOT_FOUND,      AWS_IOT_JOBS_VERSION_MISMATCH,
        AWS_IOT_JOBS_INTERNAL_ERROR, AWS_IOT_JOBS_THROTTLED,      AWS_IOT_JOBS_TERMINAL_STATE
    };

    for( i = 0; i < ( sizeof( pApiErrors ) / sizeof( pApiErrors[ 0 ] ) ); i++ )
    {
        pMessage = AwsIotJobs_strerror( pApiErrors[ i ] );
        TEST_ASSERT_NOT_NULL( pMessage );

        TEST_ASSERT_NOT_EQUAL( 0, strncmp( pInvalidStatus, pMessage, invalidStatusLength ) );
    }

    /* Check an invalid status. */
    pMessage = AwsIotJobs_strerror( ( AwsIotJobsError_t ) -1 );
    TEST_ASSERT_EQUAL_STRING( pInvalidStatus, pMessage );

    /* For each Jobs State, check the returned string. */
    i = 0;
    const char * pInvalidState = "INVALID STATE";
    size_t invalidStateLength = strlen( pInvalidState );

    while( true )
    {
        pMessage = AwsIotJobs_StateName( ( AwsIotJobState_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( pInvalidState, pMessage, invalidStateLength ) == 0 )
        {
            break;
        }

        i++;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Jobs operation functions with various
 * invalid #AwsIotJobsRequestInfo_t.
 */
TEST( Jobs_Unit_API, OperationInvalidRequestInfo )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsOperation_t operation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;

    /* Uninitialized MQTT connection. */
    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         0,
                                         NULL,
                                         NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.mqttConnection = _pMqttConnection;

    /* Invalid Thing Name. */
    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         0,
                                         NULL,
                                         NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.pThingName = TEST_THING_NAME;
    requestInfo.thingNameLength = TEST_THING_NAME_LENGTH;

    /* No reference with waitable operation. */
    status = AwsIotJobs_StartNextAsync( &requestInfo,
                                        &updateInfo,
                                        AWS_IOT_JOBS_FLAG_WAITABLE,
                                        NULL,
                                        NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Malloc function not set. */
    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         AWS_IOT_JOBS_FLAG_WAITABLE,
                                         NULL,
                                         &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.mallocResponse = IotTest_Malloc;

    /* Both callback and waitable flag set. */
    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         AWS_IOT_JOBS_FLAG_WAITABLE,
                                         &callbackInfo,
                                         &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Callback function not set. */
    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         0,
                                         &callbackInfo,
                                         NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Client token length not set. */
    requestInfo.pClientToken = "test";
    requestInfo.clientTokenLength = 0;
    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         AWS_IOT_JOBS_FLAG_WAITABLE,
                                         0,
                                         &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Client token too long. */
    requestInfo.clientTokenLength = AWS_IOT_CLIENT_TOKEN_MAX_LENGTH + 1;

    status = AwsIotJobs_GetPendingAsync( &requestInfo,
                                         0,
                                         NULL,
                                         NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.pClientToken = AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE;

    /* Job ID not set. */
    status = AwsIotJobs_DescribeAsync( &requestInfo,
                                       AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
                                       false,
                                       0,
                                       NULL,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Job ID too long. */
    requestInfo.pJobId = "jobid";
    requestInfo.jobIdLength = JOBS_MAX_ID_LENGTH + 1;

    status = AwsIotJobs_UpdateAsync( &requestInfo,
                                     &updateInfo,
                                     0,
                                     NULL,
                                     NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Using $next with UPDATE is invalid. */
    requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
    requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

    status = AwsIotJobs_UpdateAsync( &requestInfo,
                                     &updateInfo,
                                     0,
                                     NULL,
                                     NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Jobs operation functions with various
 * invalid #AwsIotJobsUpdateInfo_t.
 */
TEST( Jobs_Unit_API, OperationInvalidUpdateInfo )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;

    /* Set the members of the request info. */
    requestInfo.mqttConnection = _pMqttConnection;
    requestInfo.pThingName = TEST_THING_NAME;
    requestInfo.thingNameLength = TEST_THING_NAME_LENGTH;
    requestInfo.mallocResponse = IotTest_Malloc;

    /* Negative, invalid step timeout. */
    updateInfo.stepTimeoutInMinutes = -5;
    status = AwsIotJobs_StartNextAsync( &requestInfo,
                                        &updateInfo,
                                        0,
                                        NULL,
                                        NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Step timeout too large. */
    updateInfo.stepTimeoutInMinutes = JOBS_MAX_TIMEOUT + 1;
    status = AwsIotJobs_StartNextAsync( &requestInfo,
                                        &updateInfo,
                                        0,
                                        NULL,
                                        NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    updateInfo.stepTimeoutInMinutes = AWS_IOT_JOBS_NO_TIMEOUT;

    /* Status details length not set. */
    updateInfo.pStatusDetails = "test";
    status = AwsIotJobs_StartNextAsync( &requestInfo,
                                        &updateInfo,
                                        0,
                                        NULL,
                                        NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Status details too large. */
    updateInfo.statusDetailsLength = JOBS_MAX_STATUS_DETAILS_LENGTH + 1;

    status = AwsIotJobs_StartNextAsync( &requestInfo,
                                        &updateInfo,
                                        0,
                                        NULL,
                                        NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    updateInfo.pStatusDetails = AWS_IOT_JOBS_NO_STATUS_DETAILS;

    /* Invalid UPDATE state. */
    updateInfo.newStatus = AWS_IOT_JOB_STATE_QUEUED;
    requestInfo.pJobId = "jobid";
    requestInfo.jobIdLength = 5;

    status = AwsIotJobs_UpdateAsync( &requestInfo,
                                     &updateInfo,
                                     0,
                                     NULL,
                                     NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    updateInfo.newStatus = AWS_IOT_JOB_STATE_IN_PROGRESS;

    /* Invalid UPDATE Job ID. */
    requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
    requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

    status = AwsIotJobs_UpdateAsync( &requestInfo,
                                     &updateInfo,
                                     0,
                                     NULL,
                                     NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_wait with various
 * invalid parameters.
 */
TEST( Jobs_Unit_API, WaitInvalidParameters )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    _jobsOperation_t operation = { .link = { 0 } };

    /* NULL reference. */
    status = AwsIotJobs_Wait( NULL, 0, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* No waitable flag set. */
    status = AwsIotJobs_Wait( &operation, 0, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* NULL output parameter. */
    operation.flags = AWS_IOT_JOBS_FLAG_WAITABLE;
    status = AwsIotJobs_Wait( &operation, 0, NULL );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_getpendingasync when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, GetPendingMallocFail )
{
    _jobsMallocFail( JOBS_GET_PENDING );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_startnextasync when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, StartNextMallocFail )
{
    _jobsMallocFail( JOBS_START_NEXT );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_describeasync when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, DescribeMallocFail )
{
    _jobsMallocFail( JOBS_DESCRIBE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_updateasync when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, UpdateMallocFail )
{
    _jobsMallocFail( JOBS_UPDATE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_removepersistentsubscriptions
 * with various parameters.
 */
TEST( Jobs_Unit_API, RemovePersistentSubscriptions )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;

    /* MQTT connection not set. */
    status = AwsIotJobs_RemovePersistentSubscriptions( &requestInfo,
                                                       AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.mqttConnection = _pMqttConnection;

    /* Thing Name not set. */
    status = AwsIotJobs_RemovePersistentSubscriptions( &requestInfo,
                                                       AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.pThingName = TEST_THING_NAME;
    requestInfo.thingNameLength = TEST_THING_NAME_LENGTH;

    /* Job ID not set for DESCRIBE/UPDATE. */
    status = AwsIotJobs_RemovePersistentSubscriptions( &requestInfo,
                                                       AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;

    /* Job ID too long. */
    requestInfo.jobIdLength = JOBS_MAX_ID_LENGTH + 1;
    status = AwsIotJobs_RemovePersistentSubscriptions( &requestInfo,
                                                       AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

    /* No subscription present. */
    status = AwsIotJobs_RemovePersistentSubscriptions( &requestInfo,
                                                       AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of the Jobs callback functions.
 */
TEST( Jobs_Unit_API, SetCallback )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    _jobsSubscription_t * pSubscription = NULL;

    /* Callback info must be provided. */
    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Thing Name must be valid. */
    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, NULL, 0, 0, &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Request to remove an unspecified callback. */
    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Request to remove a callback that doesn't exist. */
    callbackInfo.function = NULL;
    callbackInfo.oldFunction = JOBS_CALLBACK_FUNCTION;

    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );

    /* Set new callback. */
    callbackInfo.function = JOBS_CALLBACK_FUNCTION;
    callbackInfo.oldFunction = NULL;

    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );

    /* Check that new callback was set. */
    pSubscription = _AwsIotJobs_FindSubscription( TEST_THING_NAME, TEST_THING_NAME_LENGTH, false );
    TEST_ASSERT_NOT_NULL( pSubscription );
    TEST_ASSERT_EQUAL_PTR( pSubscription->callbacks[ NOTIFY_NEXT_CALLBACK ].function, JOBS_CALLBACK_FUNCTION );

    /* Replace existing function. */
    callbackInfo.function = JOBS_CALLBACK_FUNCTION_2;
    callbackInfo.oldFunction = JOBS_CALLBACK_FUNCTION;

    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );

    /* Check that callback was replaced. */
    pSubscription = _AwsIotJobs_FindSubscription( TEST_THING_NAME, TEST_THING_NAME_LENGTH, false );
    TEST_ASSERT_NOT_NULL( pSubscription );
    TEST_ASSERT_EQUAL_PTR( pSubscription->callbacks[ NOTIFY_NEXT_CALLBACK ].function, JOBS_CALLBACK_FUNCTION_2 );

    /* Remove callback function. */
    callbackInfo.function = NULL;
    callbackInfo.oldFunction = JOBS_CALLBACK_FUNCTION_2;

    status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection, TEST_THING_NAME, TEST_THING_NAME_LENGTH, 0, &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_SUCCESS, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of the Jobs set callback functions when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, SetCallbackMallocFail )
{
    int32_t i = 0, mqttErrorCount = 0;
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;

    /* Set a short timeout so this test runs faster. */
    _AwsIotJobsMqttTimeoutMs = 75;

    /* A non-NULL callback function. */
    callbackInfo.function = JOBS_CALLBACK_FUNCTION;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call Jobs set callback. Memory allocation will fail at various times
         * during this call. */
        status = AwsIotJobs_SetNotifyNextCallback( _pMqttConnection,
                                                   TEST_THING_NAME,
                                                   TEST_THING_NAME_LENGTH,
                                                   0,
                                                   &callbackInfo );

        if( status == AWS_IOT_JOBS_SUCCESS )
        {
            break;
        }
        else if( status == AWS_IOT_JOBS_MQTT_ERROR )
        {
            mqttErrorCount++;
        }
        else
        {
            TEST_ASSERT_EQUAL( AWS_IOT_JOBS_NO_MEMORY, status );
        }
    }

    /* Allow 1 MQTT error, caused by failure to allocate memory for a SUBACK. */
    CHECK_MQTT_ERROR_COUNT( 1, mqttErrorCount );
}

/*-----------------------------------------------------------*/
