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
 * @file aws_iot_tests_onboarding_api.c
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
 * @brief Test user-callback to pass in #AwsIotOnboardingCallbackInfo_t.
 * It validates the API provided callback parameters with the context parameter data provided by the test.
 */
static void _testOnboardingUserCallback( void * contextParam,
                                         const AwsIotOnboardingCallbackParam_t * responseInfo );

/**
 * @brief Invokes the MQTT receive callback to simulate a response received from
 * the network.
 */
static void _simulateServerResponse( void * pArgument );

/**
 * @brief Dummy user-callback to pass in #AwsIotOnboardingCallbackInfo_t.
 */
static void _dummyAwsIotOnboardingCallback( void * contextParam,
                                            const AwsIotOnboardingCallbackParam_t * responseInfo );

/**
 * @brief Common test logic for simulating server response and calling the Onboarding libarary API under test.
 *
 * @param[in] pServerResponseInfo The server response to inject into the MQTT stack for the test case.
 * @param[in] serverResponseTimerPeriodMs The server response delay (in milliseconds) to simulate.
 * @param[in] operationType This is used to determine the Onboarding library API to call.
 * @param[in] pTestCallback The callback object to pass to the API under test.
 * @param[in] expectedStatus This will be compared against the returned status from the API call.
 */
static void _testAPIWithServerResponse( _serverResponseThreadContext_t * pServerResponseInfo,
                                        uint32_t serverResponseTimerPeriodMs,
                                        _onboardingOperationType_t operationType,
                                        const AwsIotOnboardingCallbackInfo_t * pTestCallback,
                                        AwsIotOnboardingError_t expectedStatus );

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
static const uint32_t _testOnboardingServerResponseThreadTimeoutMs = 90;

/**
 * @brief The accepted response topic for the GetDeviceCredentials service API.
 */
static const char * _getDeviceCredentialsRejectedResponseTopic =
    ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER "/rejected";

/**
 * @brief The rejected response topic for the OnboardingDevice service API.
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
static AwsIotOnboardingCallbackParam_t _expectedGetDeviceCredentialsCallbackParams =
{
    .callbackType                                    =
        AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE,
    .u.deviceCredentialsInfo.pDeviceCertificate      = ( const char * )
                                                       &_sampleGetDeviceCredentialsServerResponsePayload[ 17 ],
    .u.deviceCredentialsInfo.deviceCertificateLength = 7,
    .u.deviceCredentialsInfo.pCertificateId          = ( const char * )
                                                       &_sampleGetDeviceCredentialsServerResponsePayload[ 39 ],
    .u.deviceCredentialsInfo.certificateIdLength     = 6,
    .u.deviceCredentialsInfo.pPrivateKey             = ( const char * )
                                                       &_sampleGetDeviceCredentialsServerResponsePayload[ 57 ],
    .u.deviceCredentialsInfo.privateKeyLength        = 10
};

/**
 * @brief Callback object with #_expectedGetDeviceCredentialsCallbackParams as context parameter to test
 * #AwsIotOnboarding_GetDeviceCredentials API.
 */
static const AwsIotOnboardingCallbackInfo_t _acceptedResponseCallbackForGetDeviceCredentialsAPI =
{
    .userParam = &_expectedGetDeviceCredentialsCallbackParams,
    .function  = _testOnboardingUserCallback
};

/**
 * @brief Certificate ID for OnboardDevice API tests.
 */
static const char * _testCertificateId = "TestCertificateID";

/**
 * @brief Template ID for OnboardDevice API tests.
 */
#define _testTemplateId    "123456789123456789123456789123456789"

/**
 * @brief The rejected response topic for the OnboardDevice service API.
 */
static const char * _onboardDeviceAcceptedResponseTopic = "onboarding-templates/"_testTemplateId
                                                          "/onboard/cbor/accepted";

/**
 * @brief The accepted response topic for the OnboardDevice service API.
 */
static const char * _onboardDeviceRejectedResponseTopic = "onboarding-templates/"_testTemplateId
                                                          "/onboard/cbor/rejected";

/**
 * @brief Sample CBOR encoded response of OnboardDevice service API containing device configuration and Iot Thing name
 * data.
 */
static const uint8_t _sampleOnboardDeviceResponsePayload[] =
{
    0xA2,                                                 /* # map(2) */
    0x73,                                                 /* # text(19) */
    0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61, 0x74,
    0x69, 0x6F, 0x6E,                                     /* # "deviceConfiguration" */
    0xA2,                                                 /* # map(2), */
    0x61,                                                 /* # text(1), */
    0x31,                                                 /* # "1", */
    0x63,                                                 /* # text(2), */
    0x32, 0x33, 0x34,                                     /* # "23", */
    0x61,                                                 /* # text(1), */
    0x34,                                                 /* # "4", */
    0x62,                                                 /* # text(3), */
    0x35, 0x36,                                           /* # "567", */
    0x69,                                                 /* # text(9) */
    0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
    0x69,                                                 /* # text(9) */
    0x54, 0x65, 0x73, 0x74, 0x54, 0x68, 0x69, 0x6E, 0x67  /* # "TestThing" */
};

static const AwsIotOnboardingResponseDeviceConfigurationEntry_t _expectedDeviceConfigList[] =
{
    {
        ( const char * ) &_sampleOnboardDeviceResponsePayload[ 23 ],
        1,
        ( const char * ) &_sampleOnboardDeviceResponsePayload[ 25 ],
        3
    },
    {
        ( const char * ) &_sampleOnboardDeviceResponsePayload[ 29 ],
        1,
        ( const char * ) &_sampleOnboardDeviceResponsePayload[ 31 ],
        2
    }
};

/**
 * @brief Expected parameters that should be passed to the user-callback provided to the #AwsIotOnboarding_OnboardDevice
 * API.
 */
static AwsIotOnboardingCallbackParam_t _expectedOnboardDeviceCallbackParams =
{
    .callbackType                                      = AWS_IOT_ONBOARDING_ONBOARD_DEVICE_COMPLETE,
    .u.onboardDeviceResponse.pThingName                = ( const char * ) &_sampleOnboardDeviceResponsePayload[ 44 ],
    .u.onboardDeviceResponse.thingNameLength           = 9,
    .u.onboardDeviceResponse.pDeviceConfigList         = _expectedDeviceConfigList,
    .u.onboardDeviceResponse.numOfConfigurationEntries = sizeof( _expectedDeviceConfigList ) /
                                                         sizeof( AwsIotOnboardingResponseDeviceConfigurationEntry_t )
};

/**
 * @brief Callback object with #_expectedOnboardDeviceCallbackParams as context parameter to test
 * #AwsIotOnboarding_OnboardDevice API.
 */
static const AwsIotOnboardingCallbackInfo_t _acceptedResponseCallbackForOnboardDeviceAPI =
{
    .userParam = &_expectedOnboardDeviceCallbackParams,
    .function  = _testOnboardingUserCallback
};

/*-----------------------------------------------------------*/

static void _dummyAwsIotOnboardingCallback( void * contextParam,
                                            const AwsIotOnboardingCallbackParam_t * responseInfo )
{
    ( void ) contextParam;
    ( void ) responseInfo;
}

/*-----------------------------------------------------------*/

static void _testOnboardingUserCallback( void * contextParam,
                                         const AwsIotOnboardingCallbackParam_t * responseInfo )
{
    AwsIotOnboardingCallbackParam_t * expectedParameters = contextParam;

    AwsIotOnboarding_Assert( expectedParameters->callbackType == responseInfo->callbackType );

    switch( expectedParameters->callbackType )
    {
        case AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE:
            AwsIotOnboarding_Assert(
                expectedParameters->u.deviceCredentialsInfo.deviceCertificateLength ==
                responseInfo->u.deviceCredentialsInfo.deviceCertificateLength );
            AwsIotOnboarding_Assert( 0 == memcmp(
                                         expectedParameters->u.deviceCredentialsInfo.
                                            pDeviceCertificate,
                                         responseInfo->u.deviceCredentialsInfo.pDeviceCertificate,
                                         expectedParameters->u.deviceCredentialsInfo.
                                            deviceCertificateLength ) );
            AwsIotOnboarding_Assert(
                expectedParameters->u.deviceCredentialsInfo.certificateIdLength ==
                responseInfo->u.deviceCredentialsInfo.certificateIdLength );
            AwsIotOnboarding_Assert( 0 == memcmp(
                                         expectedParameters->u.deviceCredentialsInfo.pCertificateId,
                                         responseInfo->u.deviceCredentialsInfo.pCertificateId,
                                         expectedParameters->u.deviceCredentialsInfo.
                                            certificateIdLength ) );
            AwsIotOnboarding_Assert( expectedParameters->u.deviceCredentialsInfo.privateKeyLength ==
                                     responseInfo->u.deviceCredentialsInfo.privateKeyLength );
            AwsIotOnboarding_Assert( 0 == memcmp(
                                         expectedParameters->u.deviceCredentialsInfo.pPrivateKey,
                                         responseInfo->u.deviceCredentialsInfo.pPrivateKey,
                                         expectedParameters->u.deviceCredentialsInfo.
                                            privateKeyLength ) );
            break;

        case AWS_IOT_ONBOARDING_ONBOARD_DEVICE_COMPLETE:
            AwsIotOnboarding_Assert(
                expectedParameters->u.onboardDeviceResponse.thingNameLength ==
                responseInfo->u.onboardDeviceResponse.thingNameLength );
            AwsIotOnboarding_Assert( 0 == memcmp(
                                         expectedParameters->u.onboardDeviceResponse.
                                            pThingName,
                                         responseInfo->u.onboardDeviceResponse.pThingName,
                                         expectedParameters->u.onboardDeviceResponse.
                                            thingNameLength ) );
            AwsIotOnboarding_Assert(
                expectedParameters->u.onboardDeviceResponse.numOfConfigurationEntries ==
                responseInfo->u.onboardDeviceResponse.numOfConfigurationEntries );

            for( size_t index = 0; index < expectedParameters->u.onboardDeviceResponse.numOfConfigurationEntries;
                 index++ )
            {
                AwsIotOnboarding_Assert( expectedParameters->u.onboardDeviceResponse.pDeviceConfigList[ index ].keyLength ==
                                         responseInfo->u.onboardDeviceResponse.pDeviceConfigList[ index ].keyLength );
                AwsIotOnboarding_Assert( 0 == memcmp(
                                             expectedParameters->u.onboardDeviceResponse.pDeviceConfigList[ index ].pKey,
                                             responseInfo->u.onboardDeviceResponse.pDeviceConfigList[ index ].pKey,
                                             expectedParameters->u.onboardDeviceResponse.
                                                pDeviceConfigList[ index ].keyLength ) );
                AwsIotOnboarding_Assert( expectedParameters->u.onboardDeviceResponse.pDeviceConfigList[ index ].valueLength ==
                                         responseInfo->u.onboardDeviceResponse.pDeviceConfigList[ index ].valueLength );
                AwsIotOnboarding_Assert( 0 == memcmp(
                                             expectedParameters->u.onboardDeviceResponse.pDeviceConfigList[ index ].pValue,
                                             responseInfo->u.onboardDeviceResponse.pDeviceConfigList[ index ].pValue,
                                             expectedParameters->u.onboardDeviceResponse.
                                                pDeviceConfigList[ index ].valueLength ) );
            }

            break;

        default:
            AwsIotOnboarding_Assert( false );
    }
}

/*-----------------------------------------------------------*/

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

    /* Release the data buffer with the MQTT's free() function as it was the MQTT internal function that allocated the
     * buffer memory. */
    IotMqtt_FreeMessage( pSerializedPublishData );
}

/*-----------------------------------------------------------*/

static void _testAPIWithServerResponse( _serverResponseThreadContext_t * pServerResponseInfo,
                                        uint32_t serverResponseTimerPeriodMs,
                                        _onboardingOperationType_t operationType,
                                        const AwsIotOnboardingCallbackInfo_t * pTestCallback,
                                        AwsIotOnboardingError_t expectedStatus )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingOnboardDeviceRequestInfo_t requestInfo;

    TEST_ASSERT_EQUAL_INT( true, IotClock_TimerCreate( &_serverResponseTimer,
                                                       _simulateServerResponse,
                                                       pServerResponseInfo ) );
    ( void ) IotClock_TimerArm( &_serverResponseTimer,
                                serverResponseTimerPeriodMs,
                                0 );

    switch( operationType )
    {
        case ONBOARDING_GET_DEVICE_CREDENTIALS:
            /* Call the API under test. */
            status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                            0,
                                                            _testOnboardingApiTimeoutMs,
                                                            pTestCallback );
            break;

        case ONBOARDING_ONBOARD_DEVICE:

            requestInfo.pDeviceCertificateId = _testCertificateId;
            requestInfo.deviceCertificateIdLength = sizeof( _testCertificateId );
            requestInfo.pTemplateIdentifier = _testTemplateId;
            requestInfo.templateIdentifierLength = strlen( _testTemplateId );
            requestInfo.pParametersStart = NULL;
            requestInfo.numOfParameters = 0;

            /* Call the API under test. */
            status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                                     &requestInfo,
                                                     _testOnboardingApiTimeoutMs,
                                                     pTestCallback );
            break;

        default:
            TEST_FAIL_MESSAGE(
                "Incorrect operation type passed to internal _testAPIWithServerResponse function." );
    }

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
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPICalledWithoutInit );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPINoServerResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPIRejectedResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPICorruptDataInResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPINominalSuccess );
    RUN_TEST_CASE( Onboarding_Unit_API, GetDeviceCredentialsAPIServerResponseAfterTimeout )
    RUN_TEST_CASE( Onboarding_Unit_API,
                   GetDeviceCredentialsAPIServerResponseAndTimeoutRaceCondition );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPIInvalidParameters );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPICalledWithoutInit );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPINoServerResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPIRejectedResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPICorruptDataInResponse );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPINominalSuccess );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPIServerResponseWithoutDeviceConfiguration );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPIServerResponseWithoutThingName );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPIServerResponseAfterTimeout );
    RUN_TEST_CASE( Onboarding_Unit_API, OnboardDeviceAPIServerResponseAndTimeoutRaceCondition );
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

        AwsIotOnboarding_Cleanup();
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
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

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
 * @brief Verifies that the API returns the expected error code when it is called without initializing the library.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPICalledWithoutInit )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    /* Reset the library to simulate the test case when the library is not initialized. */
    AwsIotOnboarding_Cleanup();

    /* Call the API under test. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    0,
                                                    _testOnboardingApiTimeoutMs,
                                                    &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_NOT_INITIALIZED, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials in case of
 * receiving no response from the server.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPINoServerResponse )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    /* We will not simulate any server response for the timeout to occur! */

    /* Call the API under test. */
    status = AwsIotOnboarding_GetDeviceCredentials( _pMqttConnection,
                                                    0,
                                                    _testOnboardingApiTimeoutMs,
                                                    &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_TIMEOUT, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when Onboarding server rejects the
 * request by publishing on the "/rejected" topic.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPIRejectedResponse )
{
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    _serverResponseThreadContext_t rejectedResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsRejectedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsRejectedResponseTopic ),
        .pPublishData       = NULL,
        .publishDataLength  = 0
    };

    _testAPIWithServerResponse( &rejectedResponse,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_GET_DEVICE_CREDENTIALS,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_SERVER_REFUSED );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when the "accepted" response sent by the
 * Onboarding service contains a corrupt payload.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPICorruptDataInResponse )
{
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

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

    _testAPIWithServerResponse( &responseWithoutCertificate,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_GET_DEVICE_CREDENTIALS,
                                &callbackInfo,
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

    _testAPIWithServerResponse( &responseWithoutPrivateKey,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_GET_DEVICE_CREDENTIALS,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_BAD_RESPONSE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials in the nominal case when
 * the server responds correctly on the "accepted" topic.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPINominalSuccess )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = _sampleGetDeviceCredentialsServerResponsePayload,
        .publishDataLength  = sizeof( _sampleGetDeviceCredentialsServerResponsePayload )
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_GET_DEVICE_CREDENTIALS,
                                &_acceptedResponseCallbackForGetDeviceCredentialsAPI,
                                AWS_IOT_ONBOARDING_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when server responds much after the
 * timeout period.
 */
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPIServerResponseAfterTimeout )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = _sampleGetDeviceCredentialsServerResponsePayload,
        .publishDataLength  = sizeof( _sampleGetDeviceCredentialsServerResponsePayload )
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingServerResponseThreadTimeoutMs * 2,
                                ONBOARDING_GET_DEVICE_CREDENTIALS,
                                &_acceptedResponseCallbackForGetDeviceCredentialsAPI,
                                AWS_IOT_ONBOARDING_TIMEOUT );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials when there is a race condition between
 * the library receiving the server response and the response timeout firing. Even in such a case, the API is expected
 * to process the response and invoke the user callback with the device credentials instead of treating the case as a
 * timeout!*/
TEST( Onboarding_Unit_API, GetDeviceCredentialsAPIServerResponseAndTimeoutRaceCondition )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _getDeviceCredentialsAcceptedResponseTopic,
        .publishTopicLength = strlen( _getDeviceCredentialsAcceptedResponseTopic ),
        .pPublishData       = _sampleGetDeviceCredentialsServerResponsePayload,
        .publishDataLength  = sizeof( _sampleGetDeviceCredentialsServerResponsePayload )
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingApiTimeoutMs,
                                ONBOARDING_GET_DEVICE_CREDENTIALS,
                                &_acceptedResponseCallbackForGetDeviceCredentialsAPI,
                                AWS_IOT_ONBOARDING_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that the API detects invalid parameters passed to it, and returns the
 * equivalent error code.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPIInvalidParameters )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    AwsIotOnboardingOnboardDeviceRequestInfo_t requestInfo =
    {
        .pDeviceCertificateId      = _testCertificateId,
        .deviceCertificateIdLength = strlen( _testCertificateId ),
        .pTemplateIdentifier       = _testTemplateId,
        .templateIdentifierLength  = strlen( _testTemplateId ),
        .pParametersStart          = NULL,
        .numOfParameters           = 0,
    };

    /* Uninitialized MQTT connection. */
    status = AwsIotOnboarding_OnboardDevice( NULL,
                                             &requestInfo,
                                             0,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Callback object is not set. */
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             &requestInfo,
                                             0,
                                             NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Callback function not set. */
    callbackInfo.function = NULL;
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             &requestInfo,
                                             0,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Invalid request data. */
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             NULL,
                                             0,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Invalid certificate data in request data. */
    requestInfo.pDeviceCertificateId = NULL;
    requestInfo.deviceCertificateIdLength = 0;
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             &requestInfo,
                                             0,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );

    /* Invalid template ID in request data. Re-assign certificate data in object. */
    requestInfo.pDeviceCertificateId = _testCertificateId;
    requestInfo.deviceCertificateIdLength = sizeof( _testCertificateId );
    requestInfo.pTemplateIdentifier = NULL;
    requestInfo.templateIdentifierLength = 0;
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             &requestInfo,
                                             0,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies that the API returns the expected error code when it is called without initializing the library.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPICalledWithoutInit )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    const AwsIotOnboardingOnboardDeviceRequestInfo_t requestInfo =
    {
        .pDeviceCertificateId      = _testCertificateId,
        .deviceCertificateIdLength = sizeof( _testCertificateId ),
        .pTemplateIdentifier       = _testTemplateId,
        .templateIdentifierLength  = strlen( _testTemplateId ),
        .pParametersStart          = NULL,
        .numOfParameters           = 0,
    };

    /* Reset the library to simulate the test case when the library is not initialized. */
    AwsIotOnboarding_Cleanup();

    /* Call the API under test. */
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             &requestInfo,
                                             _testOnboardingApiTimeoutMs,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_NOT_INITIALIZED, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_getpdevicecredentials in case of
 * receiving no response from the server.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPINoServerResponse )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;

    AwsIotOnboardingCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _dummyAwsIotOnboardingCallback
    };

    const AwsIotOnboardingOnboardDeviceRequestInfo_t requestInfo =
    {
        .pDeviceCertificateId      = _testCertificateId,
        .deviceCertificateIdLength = sizeof( _testCertificateId ),
        .pTemplateIdentifier       = _testTemplateId,
        .templateIdentifierLength  = strlen( _testTemplateId ),
        .pParametersStart          = NULL,
        .numOfParameters           = 0,
    };


    /* We will not simulate any server response for the timeout to occur! */

    /* Call the API under test. */
    status = AwsIotOnboarding_OnboardDevice( _pMqttConnection,
                                             &requestInfo,
                                             _testOnboardingApiTimeoutMs,
                                             &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_TIMEOUT, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice when Onboarding server rejects the request
 * by publishing on the "/rejected" topic.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPIRejectedResponse )
{
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    _serverResponseThreadContext_t rejectedResponse =
    {
        .pPublishTopic      = _onboardDeviceRejectedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceRejectedResponseTopic ),
        .pPublishData       = NULL,
        .publishDataLength  = 0
    };

    _testAPIWithServerResponse( &rejectedResponse,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_SERVER_REFUSED );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice API when the "accepted" response sent by the
 * Onboarding service contains a corrupt payload.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPICorruptDataInResponse )
{
    AwsIotOnboardingCallbackInfo_t callbackInfo = AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyAwsIotOnboardingCallback;

    /*************** Response Payload containing invalid device configuration entry ********************/
    const uint8_t serverResponseWithInvalidDeviceConfigEntry[] =
    {
        0xA2,                                                 /* # map(2) */
        0x73,                                                 /* # text(19) */
        0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61,
        0x74, 0x69, 0x6F, 0x6E,                               /* # "deviceConfiguration" */
        0x82,                                                 /* # array(2) */
        0x01,                                                 /* # unsigned(1) */
        0x02,                                                 /* # unsigned(2) */
        0x69,                                                 /* # text(9) */
        0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
        0x69,                                                 /* # text(9) */
        0x54, 0x65, 0x73, 0x74, 0x54, 0x68, 0x69, 0x6E, 0x67  /* # "TestThing" */
    };

    _serverResponseThreadContext_t corruptResponseContext =
    {
        .pPublishTopic      = _onboardDeviceAcceptedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceAcceptedResponseTopic ),
        .pPublishData       = serverResponseWithInvalidDeviceConfigEntry,
        .publishDataLength  = sizeof( serverResponseWithInvalidDeviceConfigEntry )
    };

    _testAPIWithServerResponse( &corruptResponseContext,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_BAD_RESPONSE );

    /***************  Response Payload with invalid Thing Name entry ********************/
    const uint8_t serverResponseWithInvalidThingNameEntry[] =
    {
        0xA2,                                                 /* # map(2) */
        0x73,                                                 /* # text(19) */
        0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61,
        0x74, 0x69, 0x6F, 0x6E,                               /* # "deviceConfiguration" */
        0xA1,                                                 /* # map(1), */
        0x61,                                                 /* # text(1), */
        0x31,                                                 /* # "1", */
        0x02,                                                 /* # unsigned(2), */
        0x69,                                                 /* # text(9) */
        0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
        0x04                                                  /* # unisgned(4) */
    };

    corruptResponseContext.pPublishData = serverResponseWithInvalidThingNameEntry;
    corruptResponseContext.publishDataLength = sizeof( serverResponseWithInvalidThingNameEntry );

    _testAPIWithServerResponse( &corruptResponseContext,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_BAD_RESPONSE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice in the nominal case when
 * the server responds correctly on the "accepted" topic.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPINominalSuccess )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _onboardDeviceAcceptedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceAcceptedResponseTopic ),
        .pPublishData       = _sampleOnboardDeviceResponsePayload,
        .publishDataLength  = sizeof( _sampleOnboardDeviceResponsePayload )
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &_acceptedResponseCallbackForOnboardDeviceAPI,
                                AWS_IOT_ONBOARDING_SUCCESS );
}
/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice in the case when
 * the server responds on the "accepted" topic but without any device configuration data in the payload.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPIServerResponseWithoutDeviceConfiguration )
{
    const uint8_t pResponseWithoutDeviceConfigData[] =
    {
        0xA1,                                                 /* # map(1) */
        0x69,                                                 /* # text(9) */
        0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
        0x69,                                                 /* # text(9) */
        0x54, 0x65, 0x73, 0x74, 0x54, 0x68, 0x69, 0x6E, 0x67  /* # "TestThing" */
    };

    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _onboardDeviceAcceptedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceAcceptedResponseTopic ),
        .pPublishData       = pResponseWithoutDeviceConfigData,
        .publishDataLength  = sizeof( pResponseWithoutDeviceConfigData )
    };

    AwsIotOnboardingCallbackParam_t expectedCallbackParams =
    {
        .callbackType                                      = AWS_IOT_ONBOARDING_ONBOARD_DEVICE_COMPLETE,
        .u.onboardDeviceResponse.pThingName                = ( const char * ) &pResponseWithoutDeviceConfigData[ 12 ],
        .u.onboardDeviceResponse.thingNameLength           = 9,
        .u.onboardDeviceResponse.pDeviceConfigList         = NULL,
        .u.onboardDeviceResponse.numOfConfigurationEntries = 0
    };

    const AwsIotOnboardingCallbackInfo_t callbackInfo =
    {
        .userParam = &expectedCallbackParams,
        .function  = _testOnboardingUserCallback
    };


    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_SUCCESS );
}

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice in the case when
 * the server responds on the "accepted" topic but without thing name entry in the payload.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPIServerResponseWithoutThingName )
{
    const uint8_t pServerResponseWithoutThingName[] =
    {
        0xA1,                   /* # map(1) */
        0x73,                   /* # text(19) */
        0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61,
        0x74, 0x69, 0x6F, 0x6E, /* # "deviceConfiguration" */
        0xA1,                   /* # map(1), */
        0x61,                   /* # text(1), */
        0x31,                   /* # "1", */
        0x61,                   /* # text(1), */
        0x32                    /* # "2" */
    };

    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _onboardDeviceAcceptedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceAcceptedResponseTopic ),
        .pPublishData       = pServerResponseWithoutThingName,
        .publishDataLength  = sizeof( pServerResponseWithoutThingName )
    };

    const AwsIotOnboardingResponseDeviceConfigurationEntry_t pExpectedDeviceConfigList[] =
    {
        {
            ( const char * ) &_sampleOnboardDeviceResponsePayload[ 23 ],
            1,
            ( const char * ) &_sampleOnboardDeviceResponsePayload[ 25 ],
            1
        }
    };

    AwsIotOnboardingCallbackParam_t expectedCallbackParams =
    {
        .callbackType                                      = AWS_IOT_ONBOARDING_ONBOARD_DEVICE_COMPLETE,
        .u.onboardDeviceResponse.pThingName                = NULL,
        .u.onboardDeviceResponse.thingNameLength           = 0,
        .u.onboardDeviceResponse.pDeviceConfigList         = pExpectedDeviceConfigList,
        .u.onboardDeviceResponse.numOfConfigurationEntries = 1
    };

    const AwsIotOnboardingCallbackInfo_t callbackInfo =
    {
        .userParam = &expectedCallbackParams,
        .function  = _testOnboardingUserCallback
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingServerResponseThreadTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &callbackInfo,
                                AWS_IOT_ONBOARDING_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice when server responds much after the timeout
 * period.
 */
TEST( Onboarding_Unit_API, OnboardDeviceAPIServerResponseAfterTimeout )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _onboardDeviceAcceptedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceAcceptedResponseTopic ),
        .pPublishData       = _sampleOnboardDeviceResponsePayload,
        .publishDataLength  = sizeof( _sampleOnboardDeviceResponsePayload )
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingServerResponseThreadTimeoutMs * 2,
                                ONBOARDING_ONBOARD_DEVICE,
                                &_acceptedResponseCallbackForOnboardDeviceAPI,
                                AWS_IOT_ONBOARDING_TIMEOUT );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref onboarding_function_onboarddevice when there is a race condition between
 * the library receiving the server response and the response timeout firing. Even in such a case, the API is expected
 * to process the response and invoke the user callback with the device credentials instead of treating the case as a
 * timeout!*/
TEST( Onboarding_Unit_API, OnboardDeviceAPIServerResponseAndTimeoutRaceCondition )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _onboardDeviceAcceptedResponseTopic,
        .publishTopicLength = strlen( _onboardDeviceAcceptedResponseTopic ),
        .pPublishData       = _sampleOnboardDeviceResponsePayload,
        .publishDataLength  = sizeof( _sampleOnboardDeviceResponsePayload )
    };

    _testAPIWithServerResponse( &serverResponse,
                                _testOnboardingApiTimeoutMs,
                                ONBOARDING_ONBOARD_DEVICE,
                                &_acceptedResponseCallbackForOnboardDeviceAPI,
                                AWS_IOT_ONBOARDING_SUCCESS );
}
