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
 * @file aws_iot_tests_shadow_api.c
 * @brief Tests for the user-facing API functions (declared in aws_iot_shadow.h).
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Shadow internal include. */
#include "private/aws_iot_shadow_internal.h"

/* Test framework includes. */
#include "unity_fixture.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

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
 * @brief Test group for Shadow API tests.
 */
TEST_GROUP( Shadow_Unit_API );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Shadow API tests.
 */
TEST_SETUP( Shadow_Unit_API )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the MQTT library. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );

    /* Initialize the Shadow library. */
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_SUCCESS, AwsIotShadow_Init( 0 ) );

    /* Initialize MQTT mock. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &_pMqttConnection ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Shadow API tests.
 */
TEST_TEAR_DOWN( Shadow_Unit_API )
{
    /* Clean up MQTT mock. */
    IotTest_MqttMockCleanup();

    /* Clean up the Shadow library. */
    AwsIotShadow_Cleanup();

    /* Clean up the MQTT library. */
    IotMqtt_Cleanup();

    /* Clean up SDK. */
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Shadow API tests.
 */
TEST_GROUP_RUNNER( Shadow_Unit_API )
{
    RUN_TEST_CASE( Shadow_Unit_API, Init );
    RUN_TEST_CASE( Shadow_Unit_API, StringCoverage );
    RUN_TEST_CASE( Shadow_Unit_API, OperationInvalidParameters );
    RUN_TEST_CASE( Shadow_Unit_API, DocumentInvalidParameters );
    RUN_TEST_CASE( Shadow_Unit_API, WaitInvalidParameters );
    RUN_TEST_CASE( Shadow_Unit_API, DeleteMallocFail );
    RUN_TEST_CASE( Shadow_Unit_API, GetMallocFail );
    RUN_TEST_CASE( Shadow_Unit_API, UpdateMallocFail );
    RUN_TEST_CASE( Shadow_Unit_API, SetCallbackMallocFail );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the function @ref shadow_function_init.
 */
TEST( Shadow_Unit_API, Init )
{
    /* Check that test set up set the default value. */
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotShadowMqttTimeoutMs );

    /* The Shadow library was already initialized by test set up. Clean it up
     * before running this test. */
    AwsIotShadow_Cleanup();

    /* Set a MQTT timeout. */
    AwsIotShadow_Init( AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS + 1 );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS + 1, _AwsIotShadowMqttTimeoutMs );

    /* Cleanup should restore the default MQTT timeout. */
    AwsIotShadow_Cleanup();
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotShadowMqttTimeoutMs );

    /* Initialize the Shadow library for test clean up. */
    AwsIotShadow_Init( 0 );
}

/*-----------------------------------------------------------*/

/**
 * @brief Provides code coverage of the Shadow enum-to-string function,
 * @ref shadow_function_strerror.
 */
TEST( Shadow_Unit_API, StringCoverage )
{
    int32_t i = 0;
    const char * pMessage = NULL;

    /* For each Shadow Error, check the returned string. */
    while( true )
    {
        pMessage = AwsIotShadow_strerror( ( AwsIotShadowError_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( "INVALID STATUS", pMessage, 14 ) == 0 )
        {
            break;
        }

        i++;
    }

    /* For each rejection reason (from the Shadow service) check the returned string. */
    const AwsIotShadowError_t rejectionReasons[] =
    {
        AWS_IOT_SHADOW_BAD_REQUEST, AWS_IOT_SHADOW_UNAUTHORIZED,      AWS_IOT_SHADOW_FORBIDDEN,
        AWS_IOT_SHADOW_NOT_FOUND,   AWS_IOT_SHADOW_CONFLICT,          AWS_IOT_SHADOW_TOO_LARGE,
        AWS_IOT_SHADOW_UNSUPPORTED, AWS_IOT_SHADOW_TOO_MANY_REQUESTS, AWS_IOT_SHADOW_SERVER_ERROR
    };

    for( i = 0; i < ( sizeof( rejectionReasons ) / sizeof( rejectionReasons[ 0 ] ) ); i++ )
    {
        pMessage = AwsIotShadow_strerror( rejectionReasons[ i ] );
        TEST_ASSERT_NOT_NULL( pMessage );

        TEST_ASSERT_NOT_EQUAL( 0, strncmp( "INVALID STATUS", pMessage, 14 ) );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow operation functions with various
 * invalid parameters.
 */
TEST( Shadow_Unit_API, OperationInvalidParameters )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowDocumentInfo_t documentInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
    AwsIotShadowOperation_t operation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
    AwsIotShadowCallbackInfo_t callbackInfo = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;

    /* Missing Thing Name. */
    status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                       NULL,
                                       0,
                                       0,
                                       NULL,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                       TEST_THING_NAME,
                                       0,
                                       0,
                                       NULL,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    status = AwsIotShadow_UpdateAsync( _pMqttConnection,
                                       &documentInfo,
                                       0,
                                       0,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* Thing Name too long. */
    status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                       TEST_THING_NAME,
                                       AWS_IOT_MAX_THING_NAME_LENGTH + 1,
                                       0,
                                       NULL,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* No reference with waitable operation. */
    status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                       TEST_THING_NAME,
                                       TEST_THING_NAME_LENGTH,
                                       AWS_IOT_SHADOW_FLAG_WAITABLE,
                                       NULL,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* Both callback and waitable flag set. */
    status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                       TEST_THING_NAME,
                                       TEST_THING_NAME_LENGTH,
                                       AWS_IOT_SHADOW_FLAG_WAITABLE,
                                       &callbackInfo,
                                       &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* No callback for non-waitable GET. */
    documentInfo.pThingName = TEST_THING_NAME;
    documentInfo.thingNameLength = TEST_THING_NAME_LENGTH;
    status = AwsIotShadow_GetAsync( _pMqttConnection,
                                    &documentInfo,
                                    0,
                                    NULL,
                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* Callback function not set. */
    status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                       TEST_THING_NAME,
                                       TEST_THING_NAME_LENGTH,
                                       0,
                                       &callbackInfo,
                                       &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow operation functions with an invalid
 * document info parameter.
 */
TEST( Shadow_Unit_API, DocumentInvalidParameters )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowDocumentInfo_t documentInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
    AwsIotShadowOperation_t operation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;

    /* Missing Thing Name. */
    status = AwsIotShadow_GetAsync( _pMqttConnection,
                                    &documentInfo,
                                    AWS_IOT_SHADOW_FLAG_WAITABLE,
                                    NULL,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );
    documentInfo.pThingName = TEST_THING_NAME;
    documentInfo.thingNameLength = TEST_THING_NAME_LENGTH;

    /* Invalid QoS. */
    documentInfo.qos = ( IotMqttQos_t ) 3;
    status = AwsIotShadow_GetAsync( _pMqttConnection,
                                    &documentInfo,
                                    AWS_IOT_SHADOW_FLAG_WAITABLE,
                                    NULL,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );
    documentInfo.qos = IOT_MQTT_QOS_0;

    /* Invalid retry parameters. */
    documentInfo.retryLimit = 1;
    status = AwsIotShadow_GetAsync( _pMqttConnection,
                                    &documentInfo,
                                    AWS_IOT_SHADOW_FLAG_WAITABLE,
                                    NULL,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );
    documentInfo.retryLimit = 0;

    /* Waitable Shadow get with no memory allocation function. */
    status = AwsIotShadow_GetAsync( _pMqttConnection,
                                    &documentInfo,
                                    AWS_IOT_SHADOW_FLAG_WAITABLE,
                                    NULL,
                                    &operation );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* Update with no document. */
    status = AwsIotShadow_UpdateAsync( _pMqttConnection,
                                       &documentInfo,
                                       0,
                                       0,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* Update with no client token. */
    documentInfo.u.update.pUpdateDocument = "{\"state\":{\"reported\":{null}}}";
    documentInfo.u.update.updateDocumentLength = 29;
    status = AwsIotShadow_UpdateAsync( _pMqttConnection,
                                       &documentInfo,
                                       0,
                                       0,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* Client token too long. */
    documentInfo.u.update.pUpdateDocument = "{\"state\":{\"reported\":{null}}},\"clientToken\": "
                                            "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"";
    documentInfo.u.update.updateDocumentLength = 146;
    status = AwsIotShadow_UpdateAsync( _pMqttConnection,
                                       &documentInfo,
                                       0,
                                       0,
                                       NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref shadow_function_wait with various
 * invalid parameters.
 */
TEST( Shadow_Unit_API, WaitInvalidParameters )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    _shadowOperation_t operation = { .link = { 0 } };

    /* NULL reference. */
    status = AwsIotShadow_Wait( NULL, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* No waitable flag set. */
    status = AwsIotShadow_Wait( &operation, 0, NULL, NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_BAD_PARAMETER, status );

    /* NULL output parameters for Shadow GET. */
    operation.flags = AWS_IOT_SHADOW_FLAG_WAITABLE;
    operation.type = SHADOW_GET;
    status = AwsIotShadow_Wait( &operation, 0, NULL, NULL );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref shadow_function_deleteasync when memory
 * allocation fails at various points.
 */
TEST( Shadow_Unit_API, DeleteMallocFail )
{
    int32_t i = 0, mqttErrorCount = 0;
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowOperation_t deleteOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;

    /* Set a short timeout so this test runs faster. */
    _AwsIotShadowMqttTimeoutMs = 75;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call Shadow DELETE. Memory allocation will fail at various times
         * during this call. */
        status = AwsIotShadow_DeleteAsync( _pMqttConnection,
                                           TEST_THING_NAME,
                                           TEST_THING_NAME_LENGTH,
                                           AWS_IOT_SHADOW_FLAG_WAITABLE,
                                           NULL,
                                           &deleteOperation );

        /* Once the Shadow DELETE call succeeds, wait for it to complete. */
        if( status == AWS_IOT_SHADOW_STATUS_PENDING )
        {
            /* No response will be received from the network, so the Shadow DELETE
             * is expected to time out. */
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_TIMEOUT,
                               AwsIotShadow_Wait( deleteOperation, 0, NULL, NULL ) );
            break;
        }

        /* Count the number of MQTT library errors. Otherwise, check that the error
         * is a "No memory" error. */
        if( status == AWS_IOT_SHADOW_MQTT_ERROR )
        {
            mqttErrorCount++;
        }
        else
        {
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_NO_MEMORY, status );
        }
    }

    /* Allow 2 MQTT library errors, which are caused by failure to allocate memory
     * for incoming packets (SUBSCRIBE, UNSUBSCRIBE). */
    CHECK_MQTT_ERROR_COUNT( 2, mqttErrorCount );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref shadow_function_getasync when memory
 * allocation fails at various points.
 */
TEST( Shadow_Unit_API, GetMallocFail )
{
    int32_t i = 0, mqttErrorCount = 0;
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowDocumentInfo_t documentInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
    AwsIotShadowOperation_t getOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
    const char * pRetrievedDocument = NULL;
    size_t retrievedDocumentSize = 0;

    /* Set a short timeout so this test runs faster. */
    _AwsIotShadowMqttTimeoutMs = 75;

    /* Set the members of the document info. */
    documentInfo.pThingName = TEST_THING_NAME;
    documentInfo.thingNameLength = TEST_THING_NAME_LENGTH;
    documentInfo.qos = IOT_MQTT_QOS_1;
    documentInfo.u.get.mallocDocument = IotTest_Malloc;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call Shadow GET. Memory allocation will fail at various times
         * during this call. */
        status = AwsIotShadow_GetAsync( _pMqttConnection,
                                        &documentInfo,
                                        AWS_IOT_SHADOW_FLAG_WAITABLE,
                                        NULL,
                                        &getOperation );

        /* Once the Shadow GET call succeeds, wait for it to complete. */
        if( status == AWS_IOT_SHADOW_STATUS_PENDING )
        {
            /* No response will be received from the network, so the Shadow GET
             * is expected to time out. */
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_TIMEOUT,
                               AwsIotShadow_Wait( getOperation,
                                                  0,
                                                  &pRetrievedDocument,
                                                  &retrievedDocumentSize ) );
            break;
        }

        /* Count the number of MQTT library errors. Otherwise, check that the error
         * is a "No memory" error. */
        if( status == AWS_IOT_SHADOW_MQTT_ERROR )
        {
            mqttErrorCount++;
        }
        else
        {
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_NO_MEMORY, status );
        }
    }

    /* Allow 3 MQTT library errors, which are caused by failure to allocate memory
     * for incoming packets (SUBSCRIBE, PUBLISH, UNSUBSCRIBE). */
    CHECK_MQTT_ERROR_COUNT( 3, mqttErrorCount );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref shadow_function_updateasync when memory
 * allocation fails at various points.
 */
TEST( Shadow_Unit_API, UpdateMallocFail )
{
    int32_t i = 0, mqttErrorCount = 0;
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowDocumentInfo_t documentInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
    AwsIotShadowOperation_t updateOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;

    /* Set a short timeout so this test runs faster. */
    _AwsIotShadowMqttTimeoutMs = 75;

    /* Set the members of the document info. */
    documentInfo.pThingName = TEST_THING_NAME;
    documentInfo.thingNameLength = TEST_THING_NAME_LENGTH;
    documentInfo.qos = IOT_MQTT_QOS_1;
    documentInfo.u.update.pUpdateDocument = "{\"state\":{\"reported\":{null}},\"clientToken\":\"TEST\"}";
    documentInfo.u.update.updateDocumentLength = 50;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call Shadow UPDATE. Memory allocation will fail at various times
         * during this call. */
        status = AwsIotShadow_UpdateAsync( _pMqttConnection,
                                           &documentInfo,
                                           AWS_IOT_SHADOW_FLAG_WAITABLE,
                                           NULL,
                                           &updateOperation );

        /* Once the Shadow UPDATE call succeeds, wait for it to complete. */
        if( status == AWS_IOT_SHADOW_STATUS_PENDING )
        {
            /* No response will be received from the network, so the Shadow UPDATE
             * is expected to time out. */
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_TIMEOUT,
                               AwsIotShadow_Wait( updateOperation,
                                                  0,
                                                  NULL,
                                                  NULL ) );
            break;
        }

        /* Count the number of MQTT library errors. Otherwise, check that the error
         * is a "No memory" error. */
        if( status == AWS_IOT_SHADOW_MQTT_ERROR )
        {
            mqttErrorCount++;
        }
        else
        {
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_NO_MEMORY, status );
        }
    }

    /* Allow 3 MQTT library errors, which are caused by failure to allocate memory
     * for incoming packets (SUBSCRIBE, PUBLISH, UNSUBSCRIBE). */
    CHECK_MQTT_ERROR_COUNT( 3, mqttErrorCount );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of the Shadow set callback functions when memory
 * allocation fails at various points.
 */
TEST( Shadow_Unit_API, SetCallbackMallocFail )
{
    int32_t i = 0, mqttErrorCount = 0;
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowCallbackInfo_t callbackInfo = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;

    /* Set a short timeout so this test runs faster. */
    _AwsIotShadowMqttTimeoutMs = 75;

    /* A non-NULL callback function. */
    callbackInfo.function = ( void ( * )( void *, AwsIotShadowCallbackParam_t * ) ) 0x01;

    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        /* Call Shadow set callback. Memory allocation will fail at various times
         * during this call. */
        status = AwsIotShadow_SetDeltaCallback( _pMqttConnection,
                                                TEST_THING_NAME,
                                                TEST_THING_NAME_LENGTH,
                                                0,
                                                &callbackInfo );

        if( status == AWS_IOT_SHADOW_SUCCESS )
        {
            break;
        }
        else if( status == AWS_IOT_SHADOW_MQTT_ERROR )
        {
            mqttErrorCount++;
        }
        else
        {
            TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_NO_MEMORY, status );
        }
    }

    /* Allow 1 MQTT error, caused by failure to allocate memory for a SUBACK. */
    CHECK_MQTT_ERROR_COUNT( 1, mqttErrorCount );
}

/*-----------------------------------------------------------*/
