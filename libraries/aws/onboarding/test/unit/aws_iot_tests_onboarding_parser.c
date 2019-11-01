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
    0x78, 0x2D,                                                                         /*# text(45) */
    0x4F, 0x6F, 0x70, 0x73, 0x21, 0x20, 0x57, 0x65, 0x20, 0x68, 0x61, 0x76, 0x65,
    0x20, 0x61, 0x20, 0x6C, 0x6F, 0x6E, 0x67, 0x20, 0x65, 0x72, 0x72, 0x6F, 0x72,
    0x20, 0x6D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x2E, 0x2E, 0x2E, 0x2E, 0x2E,
    0x2E, 0x2E, 0x2E, 0x2E, 0x2E, 0x2E /*# "Oops! We have a long error message..........." */
};

/**
 * @brief The expected parsed "rejected" response data from the #_sampleRejectedServerResponsePayload sample payload.
 */
static const AwsIotOnboardingServerStatusCode_t _expectedStatusCode =
    AWS_IOT_ONBOARDING_SERVER_STATUS_INTERNAL_SERVER_ERROR; /* Status Code 500 */
static AwsIotOnboardingRejectedResponse_t _expectedParsedParams =
{
    .pErrorCode         = ( const char * ) &_sampleRejectedServerResponsePayload[ 26 ],
    .errorCodeLength    = 14,
    .pErrorMessage      = ( const char * ) &_sampleRejectedServerResponsePayload[ 55 ],
    .errorMessageLength = 45
};

/**
 * @brief Sample CBOR encoded response payload of device credentials from the server.
 */
const uint8_t _sampleDeviceCredentialsResponse[] =
{
    0xA3,                                                                               /* # map( 3 ) */
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
    0x67,                                                                               /* # text(7) */
    0x53, 0x65, 0x63, 0x72, 0x65, 0x74, 0x21                                            /*# "Secret!" */
};

/**
 * @brief Parameters that represent the expected parsing of device credentials to be done by the parser in the test.
 * This will be provided as a context parameter in the callback object supplied to the parser in the test.
 */
AwsIotOnboardingGetDeviceCredentialsResponse_t _expectedDeviceCredentialsParsedParams =
{
    .statusCode                                 = AWS_IOT_ONBOARDING_SERVER_STATUS_ACCEPTED,
    .u.acceptedResponse.pDeviceCertificate      = ( const char * )
                                                  &_sampleDeviceCredentialsResponse[ 17 ],
    .u.acceptedResponse.deviceCertificateLength = 7,
    .u.acceptedResponse.pCertificateId          = ( const char * )
                                                  &_sampleDeviceCredentialsResponse[ 39 ],
    .u.acceptedResponse.certificateIdLength     = 6,
    .u.acceptedResponse.pPrivateKey             = ( const char * )
                                                  &_sampleDeviceCredentialsResponse[ 57 ],
    .u.acceptedResponse.privateKeyLength        = 7
};

/*-----------------------------------------------------------*/

/**
 * @brief Common utility to verify that the parsed "rejected" response data passed to the callback
 * matches the expected parameters.
 */
static void _verifyParsedRejectedResponse( const AwsIotOnboardingRejectedResponse_t * pExpectedData,
                                           const AwsIotOnboardingRejectedResponse_t * pParsedData );


/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testGetDeviceCredentialsRejectedCallback( void * contextParam,
                                                       const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo );

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testGetDeviceCredentialsAcceptedCallback( void * contextParam,
                                                       const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo );

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testOnboardRejectedDeviceCallback( void * contextParam,
                                                const AwsIotOnboardingOnboardDeviceResponse_t * pResponseInfo );


/*-----------------------------------------------------------*/

static void _verifyParsedRejectedResponse( const AwsIotOnboardingRejectedResponse_t * pExpectedData,
                                           const AwsIotOnboardingRejectedResponse_t * pParsedData )
{
    /* Verify that the rejected response was parsed as expected. */
    AwsIotOnboarding_Assert( pParsedData->errorCodeLength == pExpectedData->errorCodeLength );
    AwsIotOnboarding_Assert( 0 == memcmp( pParsedData->pErrorCode,
                                          pExpectedData->pErrorCode,
                                          pExpectedData->errorCodeLength ) );
    AwsIotOnboarding_Assert( pParsedData->errorMessageLength == pExpectedData->errorMessageLength );
    AwsIotOnboarding_Assert( 0 == memcmp( pParsedData->pErrorMessage,
                                          pExpectedData->pErrorMessage,
                                          pExpectedData->errorMessageLength ) );
}

/*-----------------------------------------------------------*/

static void _testGetDeviceCredentialsRejectedCallback( void * contextParam,
                                                       const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo )
{
    AwsIotOnboardingRejectedResponse_t * pExpectedParams =
        ( AwsIotOnboardingRejectedResponse_t * ) contextParam;

    AwsIotOnboarding_Assert( pResponseInfo->statusCode == _expectedStatusCode );
    /* Verify that the rejected response was parsed as expected. */
    _verifyParsedRejectedResponse( pExpectedParams, &pResponseInfo->u.rejectedResponse );
}

/*-----------------------------------------------------------*/

static void _testGetDeviceCredentialsAcceptedCallback( void * contextParam,
                                                       const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo )
{
    AwsIotOnboardingGetDeviceCredentialsResponse_t * pExpectedParams =
        ( AwsIotOnboardingGetDeviceCredentialsResponse_t * ) contextParam;

    /* Verify that the rejected response was parsed as expected. */
    AwsIotOnboarding_Assert( pResponseInfo->statusCode == AWS_IOT_ONBOARDING_SERVER_STATUS_ACCEPTED );

    AwsIotOnboarding_Assert(
        pExpectedParams->u.acceptedResponse.deviceCertificateLength ==
        pResponseInfo->u.acceptedResponse.deviceCertificateLength );
    AwsIotOnboarding_Assert( pExpectedParams->u.acceptedResponse.pDeviceCertificate ==
                             pResponseInfo->u.acceptedResponse.pDeviceCertificate );
    AwsIotOnboarding_Assert(
        pExpectedParams->u.acceptedResponse.certificateIdLength ==
        pResponseInfo->u.acceptedResponse.certificateIdLength );
    AwsIotOnboarding_Assert( pExpectedParams->u.acceptedResponse.pCertificateId ==
                             pResponseInfo->u.acceptedResponse.pCertificateId );
    AwsIotOnboarding_Assert( pExpectedParams->u.acceptedResponse.privateKeyLength ==
                             pResponseInfo->u.acceptedResponse.privateKeyLength );
    AwsIotOnboarding_Assert( pExpectedParams->u.acceptedResponse.pPrivateKey ==
                             pResponseInfo->u.acceptedResponse.pPrivateKey );
}


/*-----------------------------------------------------------*/

static void _testOnboardRejectedDeviceCallback( void * contextParam,
                                                const AwsIotOnboardingOnboardDeviceResponse_t * pResponseInfo )
{
    AwsIotOnboardingRejectedResponse_t * pExpectedParams = ( AwsIotOnboardingRejectedResponse_t * ) contextParam;

    AwsIotOnboarding_Assert( pResponseInfo->statusCode == _expectedStatusCode );

    /* Verify that the rejected response was parsed as expected. */
    _verifyParsedRejectedResponse( pExpectedParams, &pResponseInfo->u.rejectedResponse );
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
    RUN_TEST_CASE( Onboarding_Unit_Parser, TestParseDeviceCredentialsAcceptedResponse );
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
    wrapperCallback.getDeviceCredentialsCallback.function = _testGetDeviceCredentialsRejectedCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SERVER_REFUSED, _AwsIotOnboarding_ParseDeviceCredentialsResponse( AWS_IOT_REJECTED,
                                                                                                            _sampleRejectedServerResponsePayload,
                                                                                                            sizeof( _sampleRejectedServerResponsePayload ),
                                                                                                            &wrapperCallback ) );
}

/**
 * @brief Verifies the parser function (_AwsIotOnboarding_ParseDeviceCredentialsResponse) can parse the device
 * credentials response sent by the server.
 */
TEST( Onboarding_Unit_Parser, TestParseDeviceCredentialsAcceptedResponse )
{
    _onboardingCallbackInfo_t wrapperCallback;

    wrapperCallback.getDeviceCredentialsCallback.userParam = &_expectedDeviceCredentialsParsedParams;
    wrapperCallback.getDeviceCredentialsCallback.function = _testGetDeviceCredentialsAcceptedCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS, _AwsIotOnboarding_ParseDeviceCredentialsResponse( AWS_IOT_ACCEPTED,
                                                                                                     _sampleDeviceCredentialsResponse,
                                                                                                     sizeof( _sampleDeviceCredentialsResponse ),
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
    wrapperCallback.onboardDeviceCallback.function = _testOnboardRejectedDeviceCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SERVER_REFUSED, _AwsIotOnboarding_ParseOnboardDeviceResponse( AWS_IOT_REJECTED,
                                                                                                        _sampleRejectedServerResponsePayload,
                                                                                                        sizeof( _sampleRejectedServerResponsePayload ),
                                                                                                        &wrapperCallback ) );
}
