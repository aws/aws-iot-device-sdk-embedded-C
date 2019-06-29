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
#define TEST_THING_NAME           "TestThingName"

/**
 * @brief The length of #TEST_THING_NAME.
 */
#define TEST_THING_NAME_LENGTH    ( sizeof( TEST_THING_NAME ) - 1 )

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
                status = AwsIotJobs_GetPending( &requestInfo,
                                                AWS_IOT_JOBS_FLAG_WAITABLE,
                                                NULL,
                                                &operation );
                break;

            case JOBS_START_NEXT:
                status = AwsIotJobs_StartNext( &requestInfo,
                                               &updateInfo,
                                               AWS_IOT_JOBS_FLAG_WAITABLE,
                                               NULL,
                                               &operation );
                break;

            case JOBS_DESCRIBE:
                status = AwsIotJobs_Describe( &requestInfo,
                                              AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
                                              false,
                                              AWS_IOT_JOBS_FLAG_WAITABLE,
                                              NULL,
                                              &operation );
                break;

            default:
                /* The only remaining valid type is update. */
                TEST_ASSERT_EQUAL( JOBS_UPDATE, type );

                status = AwsIotJobs_Update( &requestInfo,
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
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the function @ref jobs_function_init.
 */
TEST( Jobs_Unit_API, Init )
{
    int32_t i = 0;
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;

    /* Check that test set up set the default value. */
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotJobsMqttTimeoutMs );

    /* The Jobs library was already initialized by test set up. Clean it up
     * before running this test. */
    AwsIotJobs_Cleanup();

    /* Set a MQTT timeout. */
    AwsIotJobs_Init( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS + 1 );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS + 1, _AwsIotJobsMqttTimeoutMs );

    /* Cleanup should restore the default MQTT timeout. */
    AwsIotJobs_Cleanup();
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotJobsMqttTimeoutMs );

    /* Test jobs initialization with mutex creation failures. */
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
}

/*-----------------------------------------------------------*/

/**
 * @brief Provides code coverage of the Jobs enum-to-string functions,
 * @ref jobs_function_strerror and @ref jobs_function_statename.
 */
TEST( Jobs_Unit_API, StringCoverage )
{
    int32_t i = 0;
    const char * pMessage = NULL;

    /* For each Jobs Error, check the returned string. */
    while( true )
    {
        pMessage = AwsIotJobs_strerror( ( AwsIotJobsError_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( "INVALID STATUS", pMessage, 14 ) == 0 )
        {
            break;
        }

        i++;
    }

    /* For each Jobs State, check the returned string. */
    i = 0;

    while( true )
    {
        pMessage = AwsIotJobs_StateName( ( AwsIotJobState_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( "INVALID STATE", pMessage, 13 ) == 0 )
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
    status = AwsIotJobs_GetPending( &requestInfo,
                                    0,
                                    NULL,
                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.mqttConnection = _pMqttConnection;

    /* Invalid Thing Name. */
    status = AwsIotJobs_GetPending( &requestInfo,
                                    0,
                                    NULL,
                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.pThingName = TEST_THING_NAME;
    requestInfo.thingNameLength = TEST_THING_NAME_LENGTH;

    /* No reference with waitable operation. */
    status = AwsIotJobs_StartNext( &requestInfo,
                                   &updateInfo,
                                   AWS_IOT_JOBS_FLAG_WAITABLE,
                                   NULL,
                                   NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Malloc function not set. */
    status = AwsIotJobs_GetPending( &requestInfo,
                                    AWS_IOT_JOBS_FLAG_WAITABLE,
                                    NULL,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.mallocResponse = IotTest_Malloc;

    /* Both callback and waitable flag set. */
    status = AwsIotJobs_GetPending( &requestInfo,
                                    AWS_IOT_JOBS_FLAG_WAITABLE,
                                    &callbackInfo,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Callback function not set. */
    status = AwsIotJobs_GetPending( &requestInfo,
                                    0,
                                    &callbackInfo,
                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Client token length not set. */
    requestInfo.pClientToken = "test";
    requestInfo.clientTokenLength = 0;
    status = AwsIotJobs_GetPending( &requestInfo,
                                    AWS_IOT_JOBS_FLAG_WAITABLE,
                                    0,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Client token too long. */
    requestInfo.clientTokenLength = AWS_IOT_CLIENT_TOKEN_MAX_LENGTH + 1;

    status = AwsIotJobs_GetPending( &requestInfo,
                                    0,
                                    NULL,
                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    requestInfo.pClientToken = AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE;

    /* Job ID not set. */
    status = AwsIotJobs_Describe( &requestInfo,
                                  AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
                                  false,
                                  0,
                                  NULL,
                                  NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Job ID too long. */
    requestInfo.pJobId = "jobid";
    requestInfo.jobIdLength = JOBS_MAX_ID_LENGTH + 1;

    status = AwsIotJobs_Update( &requestInfo,
                                &updateInfo,
                                0,
                                NULL,
                                NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Using $next with UPDATE is invalid. */
    requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
    requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;

    status = AwsIotJobs_Update( &requestInfo,
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
    status = AwsIotJobs_StartNext( &requestInfo,
                                   &updateInfo,
                                   0,
                                   NULL,
                                   NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Step timeout too large. */
    updateInfo.stepTimeoutInMinutes = JOBS_MAX_TIMEOUT + 1;
    status = AwsIotJobs_StartNext( &requestInfo,
                                   &updateInfo,
                                   0,
                                   NULL,
                                   NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    updateInfo.stepTimeoutInMinutes = AWS_IOT_JOBS_NO_TIMEOUT;

    /* Status details length not set. */
    updateInfo.pStatusDetails = "test";
    status = AwsIotJobs_StartNext( &requestInfo,
                                   &updateInfo,
                                   0,
                                   NULL,
                                   NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );

    /* Status details too large. */
    updateInfo.statusDetailsLength = JOBS_MAX_STATUS_DETAILS_LENGTH + 1;

    status = AwsIotJobs_StartNext( &requestInfo,
                                   &updateInfo,
                                   0,
                                   NULL,
                                   NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_JOBS_BAD_PARAMETER, status );
    updateInfo.pStatusDetails = AWS_IOT_JOBS_NO_STATUS_DETAILS;

    /* Invalid UPDATE state. */
    requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
    requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;
    updateInfo.newStatus = AWS_IOT_JOB_STATE_QUEUED;

    status = AwsIotJobs_Update( &requestInfo,
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
 * @brief Tests the behavior of @ref jobs_function_getpending when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, GetPendingMallocFail )
{
    _jobsMallocFail( JOBS_GET_PENDING );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_startnext when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, StartNextMallocFail )
{
    _jobsMallocFail( JOBS_START_NEXT );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_describe when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, DescribeMallocFail )
{
    _jobsMallocFail( JOBS_DESCRIBE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref jobs_function_update when memory
 * allocation fails at various points.
 */
TEST( Jobs_Unit_API, UpdateMallocFail )
{
    _jobsMallocFail( JOBS_UPDATE );
}

/*-----------------------------------------------------------*/
