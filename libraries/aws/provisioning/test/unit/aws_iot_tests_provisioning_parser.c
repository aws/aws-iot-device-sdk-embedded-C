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
 * @file aws_iot_tests_provisioning_parser.c
 * @brief Tests for the parser functions internal to the Provisioning library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* AWS IoT common header include.*/
#include "aws_iot.h"

/* Provisioning internal include. */
#include "private/aws_iot_provisioning_internal.h"

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
    0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x43, 0x6F, 0x64, 0x65,                         /*# "statusCode" */
    0x19, 0x01, 0xF4,                                                                   /*# unsigned(500) */
    0x69,                                                                               /*# text(9) */
    0x65, 0x72, 0x72, 0x6F, 0x72, 0x43, 0x6F, 0x64, 0x65,                               /*# "errorCode" */
    0x6E,                                                                               /*# text(14) */
    0x49, 0x6E, 0x76, 0x61, 0x6C, 0x69, 0x64, 0x50, 0x61, 0x79, 0x6C, 0x6F, 0x61, 0x64, /*# "InvalidPayload" */
    0x6C,                                                                               /*# text(12) */
    0x65, 0x72, 0x72, 0x6F, 0x72, 0x4D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65,             /*# "errorMessage" */
    0x78, 0x2D,                                                                         /*# text(45) */
    0x4F, 0x6F, 0x70, 0x73, 0x21, 0x20, 0x57, 0x65, 0x20, 0x68, 0x61, 0x76, 0x65,
    0x20, 0x61, 0x20, 0x6C, 0x6F, 0x6E, 0x67, 0x20, 0x65, 0x72, 0x72, 0x6F, 0x72,
    0x20, 0x6D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x2E, 0x2E, 0x2E, 0x2E, 0x2E,
    0x2E, 0x2E, 0x2E, 0x2E, 0x2E, 0x2E /*# "Oops! We have a long error message..........." */
};

/**
 * @brief The expected parsed "rejected" response data from the #_sampleRejectedServerResponsePayload sample payload.
 */
static const AwsIotProvisioningServerStatusCode_t _expectedStatusCode =
    AWS_IOT_PROVISIONING_SERVER_STATUS_INTERNAL_SERVER_ERROR; /* Status Code 500 */
static AwsIotProvisioningRejectedResponse_t _expectedParsedParams =
{
    .pErrorCode         = ( const char * ) &_sampleRejectedServerResponsePayload[ 26 ],
    .errorCodeLength    = 14,
    .pErrorMessage      = ( const char * ) &_sampleRejectedServerResponsePayload[ 55 ],
    .errorMessageLength = 45
};

/**
 * @brief Sample CBOR encoded response payload of device credentials from the server.
 */
const uint8_t _sampleAcceptedKeysAndCertificateResponse[] =
{
    0xA4,                                                                               /* # map( 4 ) */
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
    0x53, 0x65, 0x63, 0x72, 0x65, 0x74, 0x21,                                           /*# "Secret!" */
    0x78, 0x19,                                                                         /*# text(25) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x4F, 0x77, 0x6E,
    0x65, 0x72, 0x73, 0x68, 0x69, 0x70, 0x54, 0x6F, 0x6B, 0x65, 0x6E,                   /*# "certificateOwnershipToken"
                                                                                         * */
    0x66,                                                                               /*# text(6) */
    0x54, 0x6F, 0x6B, 0x65, 0x6E, 0x21                                                  /*# "Token!" */
};

/**
 * @brief Parameters that represent the expected parsing of device credentials to be done by the parser in the test.
 * This will be provided as a context parameter in the callback object supplied to the parser in the test.
 */
AwsIotProvisioningCreateKeysAndCertificateResponse_t _expectedKeysAndCertificateParsedParams =
{
    .statusCode                                    = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED,
    .u.acceptedResponse.pDeviceCertificate         = ( const char * )
                                                     &_sampleAcceptedKeysAndCertificateResponse[ 17 ],
    .u.acceptedResponse.deviceCertificateLength    = 7,
    .u.acceptedResponse.pCertificateId             = ( const char * )
                                                     &_sampleAcceptedKeysAndCertificateResponse[ 39 ],
    .u.acceptedResponse.certificateIdLength        = 6,
    .u.acceptedResponse.pPrivateKey                = ( const char * )
                                                     &_sampleAcceptedKeysAndCertificateResponse[ 57 ],
    .u.acceptedResponse.privateKeyLength           = 7,
    .u.acceptedResponse.pCertificateOwnershipToken = ( const char * )
                                                     &_sampleAcceptedKeysAndCertificateResponse[ 92 ],
    .u.acceptedResponse.ownershipTokenLength       = 6,
};

/*-----------------------------------------------------------*/

/**
 * @brief Common utility to verify that the parsed "rejected" response data passed to the callback
 * matches the expected parameters.
 */
static void _verifyParsedRejectedResponse( const AwsIotProvisioningRejectedResponse_t * pExpectedData,
                                           const AwsIotProvisioningRejectedResponse_t * pParsedData );

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testCreateKeysAndCertificateRejectedCallback( void * contextParam,
                                                           const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo );

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleAcceptedKeysAndCertificateResponse as rejected
 * server response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testCreateKeysAndCertificateAcceptedCallback( void * contextParam,
                                                           const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo );

/**
 * @brief Callback for the device credentials parser that fails on being invoked. This is meant to be used for tests
 * that DO NOT expect the callback to be invoked!
 */
static void _keysAndCertificateCallbackThatFailsOnInvokation( void * contextParam,
                                                              const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo );

/**
 * @brief Test user-callback to set expectations on parsing of #_sampleRejectedServerResponsePayload as rejected server
 * response. It will be passed as context parameter in callback parameter passed in tests.
 */
static void _testRegisterThingRejectedDeviceCallback( void * contextParam,
                                                      const AwsIotProvisioningRegisterThingResponse_t * pResponseInfo );


/*-----------------------------------------------------------*/

static void _verifyParsedRejectedResponse( const AwsIotProvisioningRejectedResponse_t * pExpectedData,
                                           const AwsIotProvisioningRejectedResponse_t * pParsedData )
{
    /* Verify that the rejected response was parsed as expected. */
    AwsIotProvisioning_Assert( pParsedData->errorCodeLength == pExpectedData->errorCodeLength );
    AwsIotProvisioning_Assert( 0 == memcmp( pParsedData->pErrorCode,
                                            pExpectedData->pErrorCode,
                                            pExpectedData->errorCodeLength ) );
    AwsIotProvisioning_Assert( pParsedData->errorMessageLength == pExpectedData->errorMessageLength );
    AwsIotProvisioning_Assert( 0 == memcmp( pParsedData->pErrorMessage,
                                            pExpectedData->pErrorMessage,
                                            pExpectedData->errorMessageLength ) );
}

/*-----------------------------------------------------------*/

static void _testCreateKeysAndCertificateRejectedCallback( void * contextParam,
                                                           const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    AwsIotProvisioningRejectedResponse_t * pExpectedParams =
        ( AwsIotProvisioningRejectedResponse_t * ) contextParam;

    AwsIotProvisioning_Assert( pResponseInfo->statusCode == _expectedStatusCode );
    /* Verify that the rejected response was parsed as expected. */
    _verifyParsedRejectedResponse( pExpectedParams, &pResponseInfo->u.rejectedResponse );
}

/*-----------------------------------------------------------*/

static void _testCreateKeysAndCertificateAcceptedCallback( void * contextParam,
                                                           const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    AwsIotProvisioningCreateKeysAndCertificateResponse_t * pExpectedParams =
        ( AwsIotProvisioningCreateKeysAndCertificateResponse_t * ) contextParam;

    /* Verify that the rejected response was parsed as expected. */
    AwsIotProvisioning_Assert( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED );

    AwsIotProvisioning_Assert(
        pExpectedParams->u.acceptedResponse.deviceCertificateLength ==
        pResponseInfo->u.acceptedResponse.deviceCertificateLength );
    AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.pDeviceCertificate ==
                               pResponseInfo->u.acceptedResponse.pDeviceCertificate );
    AwsIotProvisioning_Assert(
        pExpectedParams->u.acceptedResponse.certificateIdLength ==
        pResponseInfo->u.acceptedResponse.certificateIdLength );
    AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.pCertificateId ==
                               pResponseInfo->u.acceptedResponse.pCertificateId );
    AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.privateKeyLength ==
                               pResponseInfo->u.acceptedResponse.privateKeyLength );
    AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.pPrivateKey ==
                               pResponseInfo->u.acceptedResponse.pPrivateKey );
    AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.ownershipTokenLength ==
                               pResponseInfo->u.acceptedResponse.ownershipTokenLength );
    AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.pCertificateOwnershipToken ==
                               pResponseInfo->u.acceptedResponse.pCertificateOwnershipToken );
}

/*-----------------------------------------------------------*/

static void _keysAndCertificateCallbackThatFailsOnInvokation( void * contextParam,
                                                              const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    ( void ) pResponseInfo;

    AwsIotProvisioning_Assert( false );
}

/*-----------------------------------------------------------*/

static void _testRegisterThingRejectedDeviceCallback( void * contextParam,
                                                      const AwsIotProvisioningRegisterThingResponse_t * pResponseInfo )
{
    AwsIotProvisioningRejectedResponse_t * pExpectedParams = ( AwsIotProvisioningRejectedResponse_t * ) contextParam;

    AwsIotProvisioning_Assert( pResponseInfo->statusCode == _expectedStatusCode );

    /* Verify that the rejected response was parsed as expected. */
    _verifyParsedRejectedResponse( pExpectedParams, &pResponseInfo->u.rejectedResponse );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Provisioning API tests.
 */
TEST_GROUP( Provisioning_Unit_Parser );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Provisioning API tests.
 */
TEST_SETUP( Provisioning_Unit_Parser )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the Provisioning library. */
    AwsIotProvisioning_Init( 0 );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Provisioning API tests.
 */
TEST_TEAR_DOWN( Provisioning_Unit_Parser )
{
    IotSdk_Cleanup();

    AwsIotProvisioning_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Provisioning API tests.
 */
TEST_GROUP_RUNNER( Provisioning_Unit_Parser )
{
    RUN_TEST_CASE( Provisioning_Unit_Parser, TestParseKeysAndCertificateRejectedResponse );
    RUN_TEST_CASE( Provisioning_Unit_Parser, TestParseKeysAndCertificateAcceptedResponse );
    RUN_TEST_CASE( Provisioning_Unit_Parser, TestParseKeysAndCertificateResponseWithMissingEntries );
    RUN_TEST_CASE( Provisioning_Unit_Parser, TestParseRegisterThingRejectedResponse );
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies the parser function behavior @ref _AwsIotProvisioning_ParseKeysAndCertificateResponse when the
 * Provisioning CreateKeysAndCertificate service API responds with a rejected payload.
 */
TEST( Provisioning_Unit_Parser, TestParseKeysAndCertificateRejectedResponse )
{
    _provisioningCallbackInfo_t wrapperCallback;

    wrapperCallback.createKeysAndCertificateCallback.userParam = &_expectedParsedParams;
    wrapperCallback.createKeysAndCertificateCallback.function = _testCreateKeysAndCertificateRejectedCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SERVER_REFUSED, _AwsIotProvisioning_ParseKeysAndCertificateResponse( AWS_IOT_REJECTED,
                                                                                                                 _sampleRejectedServerResponsePayload,
                                                                                                                 sizeof( _sampleRejectedServerResponsePayload ),
                                                                                                                 &wrapperCallback ) );
}

/**
 * @brief Verifies the parser function @ref _AwsIotProvisioning_ParseKeysAndCertificateResponse can parse the device
 * credentials response sent by the server.
 */
TEST( Provisioning_Unit_Parser, TestParseKeysAndCertificateAcceptedResponse )
{
    _provisioningCallbackInfo_t wrapperCallback;

    wrapperCallback.createKeysAndCertificateCallback.userParam = &_expectedKeysAndCertificateParsedParams;
    wrapperCallback.createKeysAndCertificateCallback.function = _testCreateKeysAndCertificateAcceptedCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, _AwsIotProvisioning_ParseKeysAndCertificateResponse( AWS_IOT_ACCEPTED,
                                                                                                          _sampleAcceptedKeysAndCertificateResponse,
                                                                                                          sizeof( _sampleAcceptedKeysAndCertificateResponse ),
                                                                                                          &wrapperCallback ) );
}

/**
 * @brief Verifies that the parser function @ref _AwsIotProvisioning_ParseKeysAndCertificateResponse does not call the
 * user-callback when the response payload has missing entries from the expected set of response data.
 */
TEST( Provisioning_Unit_Parser, TestParseKeysAndCertificateResponseWithMissingEntries )
{
    _provisioningCallbackInfo_t wrapperCallback;

    wrapperCallback.createKeysAndCertificateCallback.userParam = NULL;
    wrapperCallback.createKeysAndCertificateCallback.function = _testCreateKeysAndCertificateAcceptedCallback;

    /*************** Response payload only with private key ********************/
    const uint8_t payloadWithOnlyPrivateKey[] =
    {
        0xA2,                                                       /* # map( 1 ) */
        0x6A,                                                       /* # text( 10 ) */
        0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65, 0x4B, 0x65, 0x79, /* # "privateKey" */
        0x4A,                                                       /* # bytes( 10 ) */
        0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, /* # "x\x9Ax\x9Ax\x9Ax\x9Ax\x9A" */
    };

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_RESPONSE, _AwsIotProvisioning_ParseKeysAndCertificateResponse( AWS_IOT_ACCEPTED,
                                                                                                               payloadWithOnlyPrivateKey,
                                                                                                               sizeof( payloadWithOnlyPrivateKey ),
                                                                                                               &wrapperCallback ) );

    /*************** Response payload only with certificate Pem entry********************/
    const uint8_t payloadWithOnlyCertificatePem[] =
    {
        0xA1,                                                                               /* # map( 1 ) */
        0x6E,                                                                               /* # text( 14 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x50, 0x65, 0x6D, /* # "certificatePem" */
        0x67,                                                                               /* # text(7) */
        0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,                                           /* # "abcdefg" */
    };


    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_RESPONSE, _AwsIotProvisioning_ParseKeysAndCertificateResponse( AWS_IOT_ACCEPTED,
                                                                                                               payloadWithOnlyCertificatePem,
                                                                                                               sizeof( payloadWithOnlyCertificatePem ),
                                                                                                               &wrapperCallback ) );

    /*************** Response payload only with certificate ID entry********************/
    const uint8_t payloadWithOnlyCertificateId[] =
    {
        0xA1,                                                                         /* # map( 1 ) */
        0x6D,                                                                         /* # text(13) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64, /* # "certificateId" */
        0x66,                                                                         /* # text(6) */
        0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D,                                           /* # "hijklm" */
    };


    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_RESPONSE, _AwsIotProvisioning_ParseKeysAndCertificateResponse( AWS_IOT_ACCEPTED,
                                                                                                               payloadWithOnlyCertificateId,
                                                                                                               sizeof( payloadWithOnlyCertificateId ),
                                                                                                               &wrapperCallback ) );

    /*************** Response payload only with ownership token entry********************/
    const uint8_t payloadWithOnlyToken[] =
    {
        0xA1,                                                             /* # map( 1 ) */
        0x78, 0x19,                                                       /*# text(25) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x4F, 0x77, 0x6E,
        0x65, 0x72, 0x73, 0x68, 0x69, 0x70, 0x54, 0x6F, 0x6B, 0x65, 0x6E, /*# "certificateOwnershipToken"
                                                                           * */
        0x66,                                                             /*# text(6) */
        0x54, 0x6F, 0x6B, 0x65, 0x6E, 0x21                                /*# "Token!" */
    };


    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_RESPONSE, _AwsIotProvisioning_ParseKeysAndCertificateResponse( AWS_IOT_ACCEPTED,
                                                                                                               payloadWithOnlyToken,
                                                                                                               sizeof( payloadWithOnlyToken ),
                                                                                                               &wrapperCallback ) );
}


/**
 * @brief Verifies the parser function behavior (_AwsIotProvisioning_ParseRegisterThingResponse) when the
 * Provisioning RegisterThing service API responds with a rejected payload.
 */
TEST( Provisioning_Unit_Parser, TestParseRegisterThingRejectedResponse )
{
    _provisioningCallbackInfo_t wrapperCallback;

    wrapperCallback.registerThingCallback.userParam = &_expectedParsedParams;
    wrapperCallback.registerThingCallback.function = _testRegisterThingRejectedDeviceCallback;

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SERVER_REFUSED, _AwsIotProvisioning_ParseRegisterThingResponse( AWS_IOT_REJECTED,
                                                                                                            _sampleRejectedServerResponsePayload,
                                                                                                            sizeof( _sampleRejectedServerResponsePayload ),
                                                                                                            &wrapperCallback ) );
}
