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
 * @file aws_iot_tests_onboarding_parser.c
 * @brief Tests for the parser functions internal to the Onboarding library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* AWS IoT common header include.*/
#include "aws_iot.h"

/* Onboarding internal include. */
#include "private/aws_iot_onboarding_internal.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Sample CBOR encoded payload for "rejected" response from server.
 */
static const uint8_t _sampleRejectedServerResponsePayload[] =
{
    0xA3,                                                                               /*# map(3) */
    0x6A,                                                                               /*# text(10) */
    0x53, 0x74, 0x61, 0x74, 0x75, 0x73, 0x43, 0x6F, 0x64, 0x65,                         /*# "StatusCode" */
    0x19, 0x01, 0xF4,                                                                   /*# unsigned(500) */
    0x69,                                                                               /*# text(9) */
    0x45, 0x72, 0x72, 0x6F, 0x72, 0x43, 0x6F, 0x64, 0x65,                               /*# "ErrorCode" */
    0x6E,                                                                               /*# text(14) */
    0x49, 0x6E, 0x76, 0x61, 0x6C, 0x69, 0x64, 0x50, 0x61, 0x79, 0x6C, 0x6F, 0x61, 0x64, /*# "InvalidPayload" */
    0x6C,                                                                               /*# text(12) */
    0x45, 0x72, 0x72, 0x6F, 0x72, 0x4D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65,             /*# "ErrorMessage" */
    0x65,                                                                               /*# text(5) */
    0x4F, 0x6F, 0x70, 0x73, 0x21,                                                       /*# "Oops!" */
};

/**
 * @brief The expected parsed "rejected" response data from the #_sampleRejectedServerResponsePayload sample payload.
 */
static AwsIotOnboardingRejectedResponse_t _expectedParsedParams =
{
    .statusCode         = AWS_IOT_ONBOARDING_INTERNAL_SERVER_ERROR, /* Status Code 500 */
    .pErrorCode         = ( const char * ) &_sampleRejectedServerResponsePayload[ 26 ],
    .errorCodeLength    = 14,
    .pErrorMessage      = ( const char * ) &_sampleRejectedServerResponsePayload[ 54 ],
    .errorMessageLength = 5
};

/*-----------------------------------------------------------*/

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testGetDeviceCredentialsCallback( void * contextParam,
                                               const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo );

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testOnboardDeviceCallback( void * contextParam,
                                        const AwsIotOnboardingOnboardDeviceResponse_t * pResponseInfo );


/*-----------------------------------------------------------*/

static void _testGetDeviceCredentialsCallback( void * contextParam,
                                               const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo )
{
    AwsIotOnboardingRejectedResponse_t * pExpectedParams = ( AwsIotOnboardingRejectedResponse_t * ) contextParam;

    AwsIotOnboarding_Assert( pResponseInfo->operationStatus == AWS_IOT_REJECTED );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.statusCode == pExpectedParams->statusCode );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.pErrorCode == pExpectedParams->pErrorCode );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.errorCodeLength == pExpectedParams->errorCodeLength );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.pErrorMessage == pExpectedParams->pErrorMessage );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.errorMessageLength == pExpectedParams->errorMessageLength );
}

/*-----------------------------------------------------------*/

static void _testOnboardDeviceCallback( void * contextParam,
                                        const AwsIotOnboardingOnboardDeviceResponse_t * pResponseInfo )
{
    AwsIotOnboardingRejectedResponse_t * pExpectedParams = ( AwsIotOnboardingRejectedResponse_t * ) contextParam;

    AwsIotOnboarding_Assert( pResponseInfo->operationStatus == AWS_IOT_REJECTED );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.statusCode == pExpectedParams->statusCode );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.pErrorCode == pExpectedParams->pErrorCode );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.errorCodeLength == pExpectedParams->errorCodeLength );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.pErrorMessage == pExpectedParams->pErrorMessage );
    AwsIotOnboarding_Assert( pResponseInfo->u.rejectedResponse.errorMessageLength == pExpectedParams->errorMessageLength );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Onboarding API tests.
 */
TEST_GROUP( Onboarding_Unit_Parser );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Onboarding API tests.
 */
TEST_SETUP( Onboarding_Unit_Parser )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the Onboarding library. */
    AwsIotOnboarding_Init( 0 );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Onboarding API tests.
 */
TEST_TEAR_DOWN( Onboarding_Unit_Parser )
{
    IotSdk_Cleanup();

    AwsIotOnboarding_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Onboarding API tests.
 */
TEST_GROUP_RUNNER( Onboarding_Unit_Parser )
{
    RUN_TEST_CASE( Onboarding_Unit_Parser, TestParseDeviceCredentialsRejectedResponse );
    RUN_TEST_CASE( Onboarding_Unit_Parser, TestParseOnboardDeviceRejectedResponse );
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies the parser function behavior (_AwsIotOnboarding_ParseDeviceCredentialsResponse) when the
 * GetDeviceCredentials service API responds with a rejected payload.
 */
TEST( Onboarding_Unit_Parser, TestParseDeviceCredentialsRejectedResponse )
{
    _onboardingCallbackInfo_t wrapperCallback;

    wrapperCallback.getDeviceCredentialsCallback.userParam = &_expectedParsedParams;
    wrapperCallback.getDeviceCredentialsCallback.function = _testGetDeviceCredentialsCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SERVER_REFUSED, _AwsIotOnboarding_ParseDeviceCredentialsResponse( AWS_IOT_REJECTED,
                                                                                                            _sampleRejectedServerResponsePayload,
                                                                                                            sizeof( _sampleRejectedServerResponsePayload ),
                                                                                                            &wrapperCallback ) );
}

/**
 * @brief Verifies the parser function behavior (_AwsIotOnboarding_ParseOnboardDeviceResponse) when the
 * OnboardDevice service API responds with a rejected payload.
 */
TEST( Onboarding_Unit_Parser, TestParseOnboardDeviceRejectedResponse )
{
    _onboardingCallbackInfo_t wrapperCallback;

    wrapperCallback.onboardDeviceCallback.userParam = &_expectedParsedParams;
    wrapperCallback.onboardDeviceCallback.function = _testOnboardDeviceCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SERVER_REFUSED, _AwsIotOnboarding_ParseOnboardDeviceResponse( AWS_IOT_REJECTED,
                                                                                                        _sampleRejectedServerResponsePayload,
                                                                                                        sizeof( _sampleRejectedServerResponsePayload ),
                                                                                                        &wrapperCallback ) );
}
