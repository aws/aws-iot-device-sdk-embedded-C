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
 * @file aws_iot_tests_provisioning_serializer.c
 * @brief Tests for the serializer functions internal to the Provisioning library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Provisioning internal include. */
#include "private/aws_iot_provisioning_internal.h"

/* Serializer include .*/
#include "iot_serializer.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Test string to use as the Certificate-Signing Request data in CSR
 * payload serializer tests.
 */
static const char * _testCsrString = "TestCSR";

/**
 * @brief Expected serialization of the above CSR string as the request payload.
 */
static const uint8_t _expectedSerialization[] =
{
    0xA1,                                                                   /* map(1) */
    0x78, 0x19,                                                             /* text(25) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x53, 0x69,
    0x67, 0x6E, 0x69, 0x6E, 0x67, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, /* "certificateSigningRequest" */
    0x67,                                                                   /* text(7) */
    0x54, 0x65, 0x73, 0x74, 0x43, 0x53, 0x52                                /* "TestCSR" */
};

/**
 * @brief Certificate ID for Provisioning's RegisterThing Request serialization tests.
 */
static const char * _testCertificateId = "TestCertificateId";

/**
 * @brief The token string to use for Provisioning's RegisterThing Request serialization tests.
 */
static const char * _testCertificateToken = "Token!";

/**
 * @brief A sample list of parameters entries for testing serialization logic.
 */
static const AwsIotProvisioningRequestParameterEntry_t _sampleParameters[] =
{
    { "Param1", ( sizeof( "Param1" ) - 1 ), "Value1", ( sizeof( "Value1" ) - 1 ) },
    { "Param2", ( sizeof( "Param2" ) - 1 ), "Value2", ( sizeof( "Value2" ) - 1 ) },
    { "Param3", ( sizeof( "Param3" ) - 1 ), "Value3", ( sizeof( "Value3" ) - 1 ) },
};
static const size_t _numOfSampleParameters = 3;

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Provisioning API tests.
 */
TEST_GROUP( Provisioning_Unit_Serializer );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Provisioning API tests.
 */
TEST_SETUP( Provisioning_Unit_Serializer )
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
TEST_TEAR_DOWN( Provisioning_Unit_Serializer )
{
    IotSdk_Cleanup();

    AwsIotProvisioning_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Provisioning API tests.
 */
TEST_GROUP_RUNNER( Provisioning_Unit_Serializer )
{
    RUN_TEST_CASE( Provisioning_Unit_Serializer, TestSerializeCreateKeysAndCertificatePayloadNominalCase );
    RUN_TEST_CASE( Provisioning_Unit_Serializer, TestSerializeCreateCertFromCsrPayloadWithoutBuffer );
    RUN_TEST_CASE( Provisioning_Unit_Serializer, TestSerializeCreateCertFromCsrPayloadWithBuffer );
    RUN_TEST_CASE( Provisioning_Unit_Serializer, TestSerializeRegisterThingPayloadNominalCase );
    RUN_TEST_CASE( Provisioning_Unit_Serializer, TestSerializeRegisterThingPayloadCaseWithoutParameters );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that the serializer for Provisioning CreateKeysAndCertificate API generates the expected encoding for an
 * "{}" empty payload.
 */
TEST( Provisioning_Unit_Serializer, TestSerializeCreateKeysAndCertificatePayloadNominalCase )
{
    /* The request payload is an empty map container that needs. */
    const uint8_t pExpectedSerialization[] =
    {
        0xA0 /*# map( 0 ) */
    };

    uint8_t * pSerializationBuffer = NULL;
    size_t bufferSize = 0;

    /* Test the serializer function. */
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS,
                       _AwsIotProvisioning_SerializeCreateKeysAndCertificateRequestPayload( &pSerializationBuffer,
                                                                                            &bufferSize ) );
    TEST_ASSERT_NOT_NULL( pSerializationBuffer );
    TEST_ASSERT_EQUAL( sizeof( pExpectedSerialization ), bufferSize );

    /* Make sure that the serializer function generated the expected payload. */
    TEST_ASSERT_EQUAL( 0,
                       memcmp( pExpectedSerialization, pSerializationBuffer,
                               sizeof( pExpectedSerialization ) ) );

    /* Release the buffer that was allocated by the serializer function. */
    AwsIotProvisioning_FreePayload( pSerializationBuffer );
}

/**
 * @brief Tests that the CSR payload serializer calculates the serialization size, and populates the passed output
 * parameter when a serialization buffer is not passed to it.
 */
TEST( Provisioning_Unit_Serializer, TestSerializeCreateCertFromCsrPayloadWithoutBuffer )
{
    uint8_t * pSerializationBuffer = NULL;
    size_t bufferSizeNeeded = 0;

    /* Test the serializer function. */
    TEST_ASSERT_EQUAL( true,
                       _AwsIotProvisioning_SerializeCreateCertFromCsrRequestPayload( _testCsrString,
                                                                                     strlen( _testCsrString ),
                                                                                     pSerializationBuffer,
                                                                                     &bufferSizeNeeded ) );
    /* Make sure that the output parameter has been populated with the serialization size. */
    TEST_ASSERT_EQUAL( sizeof( _expectedSerialization ), bufferSizeNeeded );
}

/**
 * @brief Tests that the CSR payload serializer populates the buffer with the serialized payload, when
 * the passed buffer is valid.
 */
TEST( Provisioning_Unit_Serializer, TestSerializeCreateCertFromCsrPayloadWithBuffer )
{
    uint8_t testBuffer[ sizeof( _expectedSerialization ) ] = { 0 };
    size_t bufferSize = sizeof( testBuffer );

    /* Test the serializer function. */
    TEST_ASSERT_EQUAL( true,
                       _AwsIotProvisioning_SerializeCreateCertFromCsrRequestPayload( _testCsrString,
                                                                                     strlen( _testCsrString ),
                                                                                     &testBuffer[ 0 ],
                                                                                     &bufferSize ) );
    /* Verify the generated serialization in the buffer. */
    TEST_ASSERT_EQUAL( 0, memcmp( _expectedSerialization, testBuffer,
                                  sizeof( _expectedSerialization ) ) );
}

/**
 * @brief Tests the behavior of the serializer for generating a payload containing ONLY the "certificate" data.
 */
TEST( Provisioning_Unit_Serializer, TestSerializeRegisterThingPayloadNominalCase )
{
    AwsIotProvisioningRegisterThingRequestInfo_t testRequestInfo;

    testRequestInfo.pDeviceCertificateId = _testCertificateId;
    testRequestInfo.deviceCertificateIdLength = strlen( _testCertificateId );
    testRequestInfo.pCertificateOwnershipToken = _testCertificateToken;
    testRequestInfo.ownershipTokenLength = strlen( _testCertificateToken );
    testRequestInfo.pParametersStart = _sampleParameters;
    testRequestInfo.numOfParameters = _numOfSampleParameters;

    /**
     * @brief The expected serialized payload for Provisioning's RegisterThing API request containing #_sampleParameters and
     * #_testCertificateId.
     */
    static const uint8_t pExpectedSerialization[] =
    {
        /* *INDENT-OFF* */
        0xA3,                                                                                                 /*# map( 2 ) */
        0x6D,                                                                                                 /*# text( 13 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64,                         /*# "certificateId" */
        0x71,                                                                                                 /*# text( 17 ) */
        0x54, 0x65, 0x73, 0x74, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64, /*# "TestCertificateId" */
        0x78, 0x19,                                                                                           /*# text(25) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x4F, 0x77, 0x6E,
        0x65, 0x72, 0x73, 0x68, 0x69, 0x70, 0x54, 0x6F, 0x6B, 0x65, 0x6E,                                     /*# "certificateOwnershipToken" */
        0x66,                                                                                                 /*# text(6) */
        0x54, 0x6F, 0x6B, 0x65, 0x6E, 0x21,                                                                   /*# "Token!" */
        0x6A,                                                                                                 /*# text( 10 ) */
        0x70,0x61,0x72,0x61,0x6D,0x65,0x74,0x65,0x72,0x73,                                                    /*# "parameters" */
        0xA3,                                                                                                 /*# map(3) */
        0x66,                                                                                                 /*# text(6) */
        0x50, 0x61, 0x72, 0x61, 0x6D, 0x31,                                                                   /*# "Param1" */
        0x66,                                                                                                 /*# text(6) */
        0x56, 0x61, 0x6C, 0x75, 0x65, 0x31,                                                                   /*# "Value1" */
        0x66,                                                                                                 /*# text(6) */
        0x50, 0x61, 0x72, 0x61, 0x6D, 0x32,                                                                   /*# "Param2" */
        0x66,                                                                                                 /*# text(6) */
        0x56, 0x61, 0x6C, 0x75, 0x65, 0x32,                                                                   /*# "Value2" */
        0x66,                                                                                                 /*# text(6) */
        0x50, 0x61, 0x72, 0x61, 0x6D, 0x33,                                                                   /*# "Param3" */
        0x66,                                                                                                 /*# text(6) */
        0x56, 0x61, 0x6C, 0x75, 0x65, 0x33,                                                                   /*# "Value3" */
        /* *INDENT-ON* */
    };

    uint8_t * pSerializationBuffer = NULL;
    size_t bufferSize = 0;

    /* Test the serializer function. */
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS,
                       _AwsIotProvisioning_SerializeRegisterThingRequestPayload( &testRequestInfo,
                                                                                 &pSerializationBuffer,
                                                                                 &bufferSize ) );
    TEST_ASSERT_NOT_NULL( pSerializationBuffer );
    TEST_ASSERT_EQUAL( sizeof( pExpectedSerialization ), bufferSize );

    /* Make sure that the serializer generated the expected request payload data. */
    TEST_ASSERT_EQUAL( 0, memcmp( pExpectedSerialization, pSerializationBuffer,
                                  sizeof( pExpectedSerialization ) ) );

    /* Release the buffer memory that was allocated by the serializer function. */
    AwsIotProvisioning_FreePayload( pSerializationBuffer );
}

/**
 * @brief Tests the behavior of the serializer for generating a payload containing "certificate" and "parameters".
 */
TEST( Provisioning_Unit_Serializer, TestSerializeRegisterThingPayloadCaseWithoutParameters )
{
    AwsIotProvisioningRegisterThingRequestInfo_t testRequestInfo;

    testRequestInfo.pDeviceCertificateId = _testCertificateId;
    testRequestInfo.deviceCertificateIdLength = strlen( _testCertificateId );
    testRequestInfo.pCertificateOwnershipToken = _testCertificateToken;
    testRequestInfo.ownershipTokenLength = strlen( _testCertificateToken );
    testRequestInfo.pParametersStart = NULL;
    testRequestInfo.numOfParameters = 0;

    /**
     * @brief The expected serialized payload for Provisioning's RegisterThing API request containing #_sampleParameters and
     * #_testCertificateId.
     */
    static const uint8_t pExpectedSerializationWithoutParameters[] =
    {
        /* *INDENT-OFF* */
        0xA2,                                                                                                 /*# map( 2 ) */
        0x6D,                                                                                                 /*# text( 13 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64,                         /*# "certificateId" */
        0x71,                                                                                                 /*# text( 17 ) */
        0x54, 0x65, 0x73, 0x74, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64, /*# "TestCertificateId" */
        0x78, 0x19,                                                                                           /*# text(25) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x4F, 0x77, 0x6E,
        0x65, 0x72, 0x73, 0x68, 0x69, 0x70, 0x54, 0x6F, 0x6B, 0x65, 0x6E,                                     /*# "certificateOwnershipToken" */
        0x66,                                                                                                 /*# text(6) */
        0x54, 0x6F, 0x6B, 0x65, 0x6E, 0x21,                                                                   /*# "Token!" */
        /* *INDENT-ON* */
    };

    uint8_t * pSerializationBuffer = NULL;
    size_t bufferSize = 0;

    /* Test the serializer function. */
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS,
                       _AwsIotProvisioning_SerializeRegisterThingRequestPayload( &testRequestInfo,
                                                                                 &pSerializationBuffer,
                                                                                 &bufferSize ) );
    TEST_ASSERT_NOT_NULL( pSerializationBuffer );
    TEST_ASSERT_EQUAL( sizeof( pExpectedSerializationWithoutParameters ), bufferSize );

    /* Make sure that the serializer generated the expected request payload data. */
    TEST_ASSERT_EQUAL( 0, memcmp( pExpectedSerializationWithoutParameters, pSerializationBuffer,
                                  sizeof( pExpectedSerializationWithoutParameters ) ) );

    /* Release the buffer that was allocated by the serializer function. */
    AwsIotProvisioning_FreePayload( pSerializationBuffer );
}
