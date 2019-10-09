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
 * @file aws_iot_tests_ponboarding_api.c
 * @brief Tests for the user-facing API functions (declared in aws_iot_onboarding.h).
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Onboarding internal include. */
#include "private/aws_iot_onboarding_internal.h"

/* MQTT include. */
#include "iot_mqtt.h"
#include "private/iot_mqtt_internal.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"

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
 * @brief Context for calls to the network receive function.
 */
typedef struct _receiveContext
{
    const uint8_t * pData; /**< @brief The data to receive. */
    size_t dataLength;     /**< @brief Length of data. */
    size_t dataIndex;      /**< @brief Next byte of data to read. */
} _receiveContext_t;

/**
 * @brief Context for calls to the server response simulating thread, #_simulateServerResponse .
 */
typedef struct _serverResponseThreadContext
{
    const char * pPublishTopic;   /**< @brief The topic to simulate server PUBLISH on. */
    size_t publishTopicLength;    /**< @brief The length of the server's PUBLISH topic. */
    const uint8_t * pPublishData; /**< @brief The data to send as PUBLISH payload on the topic. */
    size_t publishDataLength;     /**< @brief The length of the PUBLISh payload. */
} _serverResponseThreadContext_t;

/**
 * @brief Parameter 1 of #_testOnboardingUserCallback.
 */
typedef struct _expectedUserCallbackParams
{
    AwsIotOnboardingCallbackType_t type;      /**< @brief Expected callback type. */
    const uint8_t * certificateDataStartIter; /**< @brief Start address/iterator to the expected certificate
                                               * data in the buffer. */
    size_t certificateDataLength;             /**< @brief Length of the expected certificate data. */
    const uint8_t * certificateIdStartIter;   /**< @brief Start address/iterator to the expected certificate
                                               * Id data in the buffer buffer. */
    size_t certificateIdLength;               /**< @brief Length of the expected certificate Id. */
    const uint8_t * privateKeyDataStartIter;  /**< @brief Start address/iterator to the expected private key
                                               * data in the buffer. */
    size_t privateKeyDataLength;              /**< @brief Length of the expected private key data. */
} _expectedUserCallbackParams_t;

/*-----------------------------------------------------------*/

/**
 * @brief The MQTT connection shared among the tests.
 */
static IotMqttConnection_t _pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/**
 * @brief Timer used to simulate a PUBLISH response from the Onboarding server.
 */
static IotTimer_t _serverResponseTimer;

/**
 * @brief The server response timeout value for operation APIs of the Onboarding library.
 */
static const uint32_t _testOnboardingApiTimeoutMs = 100;

/**
 * @brief The timer period after which the "server response simulating" thread should be run.
 */
static const uint32_t _testOnboardingServerResponseThreadTimeout_ms = 90;

/**
 * @brief The accepted response topic for the GetDeviceCredentials service API.
 */
static const char * _getDeviceCredentialsRejectedResponseTopic =
    ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER "/rejected";

/**
 * @brief The rejected response topic for the GetDeviceCredentials service API.
 */
static const char * _getDeviceCredentialsAcceptedResponseTopic =
    ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER "/accepted";

/**
 * @brief Sample CBOR encoded response of GetDeviceCredentials service API containing mock certificate and private key
 * data.
 */
static const uint8_t _sampleGetDeviceCredentialsServerResponsePayload[] =
{
    0xA3,                                                                               /* # map( 2 ) */
    0x6E,                                                                               /* # text( 14 ) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x50, 0x65, 0x6D, /* # "certificatePem" */
    0x67,                                                                               /* # text(7) */
    0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,                                           /* # "abcdefg" */
    0x6D,                                                                               /* # text(13) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64,       /* # "certificateId" */
    0x66,                                                                               /* # text(6) */
    0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D,                                                 /* # "hijklm" */
    0x6A,                                                                               /* # text( 10 ) */
    0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65, 0x4B, 0x65, 0x79,                         /* # "privateKey" */
    0x4A,                                                                               /* # bytes( 10 ) */
    0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A,                         /* #
                                                                                         * "x\x9Ax\x9Ax\x9Ax\x9Ax\x9A"*/
};

/**
 * @brief Expected parameters to the user-callback by the Onboarding library APIs.
 */
static _expectedUserCallbackParams_t _getDeviceCredentialsExpectedCallbackParams =
{
    .type                     = AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE,
    .certificateDataStartIter = &_sampleGetDeviceCredentialsServerResponsePayload[ 17 ],
    .certificateDataLength    = 7,
    .certificateIdStartIter   = &_sampleGetDeviceCredentialsServerResponsePayload[ 39 ],
    .certificateIdLength      = 6,
    .privateKeyDataStartIter  = &_sampleGetDeviceCredentialsServerResponsePayload[ 57 ],
    .privateKeyDataLength     = 10
};

/*-----------------------------------------------------------*/

/**
 * @brief Dummy user-callback to pass in #AwsIotOnboardingCallbackInfo_t.
 */
void _dummyAwsIotOnboardingCallback( void * contextParam,
                                     const AwsIotOnboardingCallbackParam_t * responseInfo )
{
    ( void ) contextParam;
    ( void ) responseInfo;
}

/**
 * @brief Test user-callback to pass in #AwsIotOnboardingCallbackInfo_t.
 * It validates the API provided callback parameters with the context parameter data provided by the test.
 */
void _testOnboardingUserCallback( void * contextParam,
                                  const AwsIotOnboardingCallbackParam_t * responseInfo )
{
    _expectedUserCallbackParams_t * expectedParameters = contextParam;

    AwsIotOnboarding_Assert( expectedParameters->type == responseInfo->callbackType );
    AwsIotOnboarding_Assert( expectedParameters->certificateDataLength ==
                             responseInfo->u.deviceCredentialsInfo.deviceCertificateLength );
    AwsIotOnboarding_Assert( 0 == memcmp( expectedParameters->certificateDataStartIter,
                                          responseInfo->u.deviceCredentialsInfo.pDeviceCertificate,
                                          expectedParameters->certificateDataLength ) );
    AwsIotOnboarding_Assert( expectedParameters->certificateIdLength ==
                             responseInfo->u.deviceCredentialsInfo.certificateIdLength );
    AwsIotOnboarding_Assert( 0 == memcmp( expectedParameters->certificateIdStartIter,
                                          responseInfo->u.deviceCredentialsInfo.pCertificateId,
                                          expectedParameters->certificateIdLength ) );
    AwsIotOnboarding_Assert( expectedParameters->privateKeyDataLength ==
                             responseInfo->u.deviceCredentialsInfo.privateKeyLength );
    AwsIotOnboarding_Assert( 0 == memcmp( expectedParameters->privateKeyDataStartIter,
                                          responseInfo->u.deviceCredentialsInfo.pPrivateKey,
                                          expectedParameters->privateKeyDataLength ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Invokes the MQTT receive callback to simulate a response received from
 * the network.
 */
static void _simulateServerResponse( void * pArgument )
{
    _serverResponseThreadContext_t * context = pArgument;
    _receiveContext_t receiveContext = { 0 };
    uint8_t * pSerializedPublishData = NULL;
    size_t serializedPublishDataLength = 0;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    publishInfo.qos = IOT_MQTT_QOS_0;
    /* Set the server response.*/
    publishInfo.pPayload = context->pPublishData;
    publishInfo.payloadLength = context->publishDataLength;
    /* Set the operation topic name. */
    publishInfo.pTopicName = context->pPublishTopic;
    publishInfo.topicNameLength = context->publishTopicLength;

    TEST_ASSERT_EQUAL_MESSAGE( IOT_MQTT_SUCCESS, _IotMqtt_SerializePublish( &publishInfo,
                                                                            &pSerializedPublishData,
                                                                            &
                                                                            serializedPublishDataLength,
                                                                            NULL,
                                                                            NULL ),
                               "Could not generate serialized publish data for injecting Onboarding server response" );

    receiveContext.pData = pSerializedPublishData;
    receiveContext.dataLength = serializedPublishDataLength;

    /* Call the MQTT receive callback to process the ACK packet. */
    IotMqtt_ReceiveCallback( &receiveContext,
                             _pMqttConnection );

    free( pSerializedPublishData );
}

/**
 * @brief Common logic for test cases on the AwsIotOnboarding_GetDeviceCredentials API that simulate server response.
 *
 * @param[in] serverResponseIndo
 */
static void _testGetDeviceCredentialsWithServerResponse(
    _serverResponseThreadContext_t * pServerResponseInfo,
    const AwsIotOnboardingCallbackInfo_t *
    pTestCallback,
    uint32_t serverResponseTimerPeriodMs,
    AwsIotOnboardingError_t expectedStatus )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;

    TEST_ASSERT_EQUAL_INT( true, IotClock_TimerCreate( &_serverResponseTimer,
                                                       _simulateServerResponse,
                                                       pServerResponseInfo ) );
    ( void ) IotClock_TimerArm( &_serverResponseTimer,
                                serverResponseTimerPeriodMs,
                                0 );

    /* Call the API under test. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    0,
                                                    _testOnboardingApiTimeoutMs,
                                                    pTestCallback );

    TEST_ASSERT_EQUAL( expectedStatus, status );

    IotClock_TimerDestroy( &_serverResponseTimer );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Onboarding API tests.
 */
TEST_GROUP( Onboarding_Unit_API );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Onboarding API tests.
 */
TEST_SETUP( Onboarding_Unit_API )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the MQTT library. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );

    /* Initialize the Onboarding library. */
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS, AwsIotOnboarding_Init( 0 ) );

    /* Initialize MQTT mock. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &_pMqttConnection ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Onboarding API tests.
 */
TEST_TEAR_DOWN( Onboarding_Unit_API )
{
    /* Clean up MQTT mock. */
    IotTest_MqttMockCleanup();

    /* Clean up libraries. */
    AwsIotOnboarding_Cleanup();
    IotMqtt_Cleanup();
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Onboarding API tests.
 */
TEST_GROUP_RUNNER( Onboarding_Unit_API )
{
    RUN_TEST_CASE( Onboarding_Unit_API, Init );
    RUN_TEST_CASE( Onboarding_Unit_API, StringCoverage );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPIInvalidParameters );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsNoServerResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsRejectedResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsCorruptDataInResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsNominalSuccess );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsServerResponseAfterTimeout );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsServerResponseAndTimeoutRaceCondition );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the function @ref onboarding_function_init.
 */
TEST( Onboarding_Unit_API, Init )
{
    int32_t i = 0;
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;

    /* Check that test set up set the default value. */
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotOnboardingMqttTimeoutMs );

    /* The Onboarding library was already initialized by test set up. Clean it up
     * before running this test. */
    AwsIotOnboarding_Cleanup();

    /* Set a MQTT timeout. */
    AwsIotOnboarding_Init( AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS + 1 );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS + 1,
                       _AwsIotOnboardingMqttTimeoutMs );

    /* Cleanup should restore the default MQTT timeout. */
    AwsIotOnboarding_Cleanup();
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotOnboardingMqttTimeoutMs );

    /* Test onboarding initialization with mutex creation failures. */
    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        status = AwsIotOnboarding_Init( 0 );

        /* Check that the status is either success or "INIT FAILED". */
        if( status == AWS_IOT_ONBOARDING_SUCCESS )
        {
            break;
        }

        TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_INIT_FAILED, status );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Provides code coverage of the Onboarding enum-to-string functions,
 * @ref onboarding_function_strerror.
 */
TEST( Onboarding_Unit_API, StringCoverage )
{
    int32_t i = 0;
    const char * pMessage = NULL;

    /* For each Onboarding Error, check the returned string. */
    while( true )
    {
        pMessage = AwsIotOnboarding_strerror( ( AwsIotOnboardingError_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( "INVALID STATUS", pMessage, 14 ) == 0 )
        {
            break;
        }

        i++;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies that the API returns the appropriate error code on passing invalid parameters.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPIInvalidParameters )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_CALLBACK_INFO_INITIALIZER;

    /* Uninitialized MQTT connection. */
    status = AwsIotOnboarding_GetDeviceCredentials( NULL,
                                                    0,
                                                    0,
                                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Unknown Security Setting. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    2,
                                                    0,
                                                    &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Callback object is not set. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    0,
                                                    0,
                                                    NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Callback function not set. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    0,
                                                    0,
                                                    &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials in case of
 * receiving no response from the server.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsNoServerResponse )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    /* We will not simulate any server response for the timeout to occur! */

    /* Call the API under test. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    0,
                                                    _testOnboardingApiTimeoutMs,
                                                    &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_TIMEOUT, status );
}

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when Onboarding server rejects the
 * request
 * by publishing on the "/rejected" topic.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsRejectedResponse )
{
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    _serverResponseThreadContext_t rejectedResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsRejectedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsRejectedResponseTopic ),
        .pPublishData       = NULL,
        .publishDataLength  = 0
    };

    _testGetDeviceCredentialsWithServerResponse( &rejectedResponse,
                                                 &callbackInfo,
                                                 _testOnboardingServerResponseThreadTimeout_ms,
                                                 AWS_IOT_ONBOARDING_SERVER_REFUSED );
}

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when the "accepted" response sent by the
 * Onboarding service contains a corrupt payload.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsCorruptDataInResponse )
{
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    /*************** Response payload without certificate entry********************/
    const uint8_t serverResponseWithoutCertificate[] =
    {
        0xA2,                                                       /* # map( 2 ) */
        0x6A,                                                       /* # text( 10 ) */
        /* THERE IS NO ENTRY FOR "CertificatePem"!! */
        0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65, 0x4B, 0x65, 0x79, /* # "privateKey" */
        0x4A,                                                       /* # bytes( 10 ) */
        0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, /* # "x\x9Ax\x9Ax\x9Ax\x9Ax\x9A" */
    };

    _serverResponseThreadContext_t responseWithoutCertificate =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = serverResponseWithoutCertificate,
        .publishDataLength  = sizeof( serverResponseWithoutCertificate )
    };

    _testGetDeviceCredentialsWithServerResponse( &responseWithoutCertificate,
                                                 &callbackInfo,
                                                 _testOnboardingServerResponseThreadTimeout_ms,
                                                 AWS_IOT_ONBOARDING_BAD_RESPONSE );

    /*************** Response payload without private key entry********************/
    const uint8_t serverResponseWithCorruptPrivateKeyEntry[] =
    {
        0xA2,                                                                               /* # map( 2 ) */
        0x6E,                                                                               /* # text( 14 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x50, 0x65, 0x6D, /* # "certificatePem" */
        0x4A,                                                                               /* # bytes( 10 ) */
        0x12, 0x34, 0x12, 0x34, 0x12, 0x34, 0x12, 0x34, 0x12, 0x34,                         /* #
                                                                                             * "\x124\x124\x124\x124\x124"
                                                                                             * */
        0x6A,                                                                               /* # text( 10 ) */
        0x50, 0x75, 0x62, 0x6C, 0x69, 0x63, 0x4B, 0x65, 0x79,                               /* # "PublicKey"  <------
                                                                                             * THIS IS CORRUPT! */
        0x4A,                                                                               /* # bytes( 10 ) */
        0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A,                         /* #
                                                                                             * "x\x9Ax\x9Ax\x9Ax\x9Ax\x9A"
                                                                                             * */
    };

    _serverResponseThreadContext_t responseWithoutPrivateKey =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = serverResponseWithCorruptPrivateKeyEntry,
        .publishDataLength  = sizeof( serverResponseWithCorruptPrivateKeyEntry )
    };

    _testGetDeviceCredentialsWithServerResponse( &responseWithoutPrivateKey,
                                                 &callbackInfo,
                                                 _testOnboardingServerResponseThreadTimeout_ms,
                                                 AWS_IOT_ONBOARDING_BAD_RESPONSE );
}

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials in the nominal case when
 * the server responds correctly on the "accepted" topic.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsNominalSuccess )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = _sampleGetDeviceCredentialsServerResponsePayload,
        .publishDataLength  = sizeof( _sampleGetDeviceCredentialsServerResponsePayload )
    };

    AwsIotOnboardingCallbackInfo_t callbackInfo =
    {
        .userParam = &_getDeviceCredentialsExpectedCallbackParams,
        .function  = _testOnboardingUserCallback
    };

    _testGetDeviceCredentialsWithServerResponse( &serverResponse,
                                                 &callbackInfo,
                                                 _testOnboardingServerResponseThreadTimeout_ms,
                                                 AWS_IOT_ONBOARDING_SUCCESS );
}

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when server responds much after the
 * timeout period.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsServerResponseAfterTimeout )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = _sampleGetDeviceCredentialsServerResponsePayload,
        .publishDataLength  = sizeof( _sampleGetDeviceCredentialsServerResponsePayload )
    };

    AwsIotOnboardingCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _dummyAwsIotOnboardingCallback
    };

    _testGetDeviceCredentialsWithServerResponse( &serverResponse,
                                                 &callbackInfo,
                                                 _testOnboardingServerResponseThreadTimeout_ms * 2,
                                                 AWS_IOT_ONBOARDING_TIMEOUT );
}

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when there is a race condition between
 * the library receiving the server response and the timeout firing. Even in such a case, the API is expected to process
 * the response and invoke the user callback with the device credentials instead of treating the case as a timeout!
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsServerResponseAndTimeoutRaceCondition )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = _sampleGetDeviceCredentialsServerResponsePayload,
        .publishDataLength  = sizeof( _sampleGetDeviceCredentialsServerResponsePayload )
    };

    AwsIotOnboardingCallbackInfo_t callbackInfo =
    {
        .userParam = &_getDeviceCredentialsExpectedCallbackParams,
        .function  = _testOnboardingUserCallback
    };

    _testGetDeviceCredentialsWithServerResponse( &serverResponse,
                                                 &callbackInfo,
                                                 _testOnboardingApiTimeoutMs,
                                                 AWS_IOT_ONBOARDING_SUCCESS );
}
