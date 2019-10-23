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
 * @file aws_iot_tests_onboarding_internal.c
 * @brief Tests for the functions internal to the Onboarding library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Onboarding internal include. */
#include "private/aws_iot_onboarding_internal.h"

/* Serializer include .*/
#include "iot_serializer.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/


/*-----------------------------------------------------------*/

/**
 * @brief Certificate ID for OnboardDevice Request serialization tests.
 */
static const char * _testCertificateId = "TestCertificateId";

/**
 * @brief A sample list of parameters entries for testing serialization logic.
 */
static const AwsIotOnboardingRequestParameterEntry_t _sampleParameters[] =
{
    { "Param1", ( sizeof( "Param1" ) - 1 ), "Value1", ( sizeof( "Value1" ) - 1 ) },
    { "Param2", ( sizeof( "Param2" ) - 1 ), "Value2", ( sizeof( "Value2" ) - 1 ) },
    { "Param3", ( sizeof( "Param3" ) - 1 ), "Value3", ( sizeof( "Value3" ) - 1 ) },
};
static const size_t _numOfSampleParameters = 3;

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Onboarding API tests.
 */
TEST_GROUP( Onboarding_Unit_Serializer );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Onboarding API tests.
 */
TEST_SETUP( Onboarding_Unit_Serializer )
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
TEST_TEAR_DOWN( Onboarding_Unit_Serializer )
{
    IotSdk_Cleanup();

    AwsIotOnboarding_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Onboarding API tests.
 */
TEST_GROUP_RUNNER( Onboarding_Unit_Serializer )
{
    RUN_TEST_CASE( Onboarding_Unit_Serializer, TestGetDeviceCredentialsSerializationNominalCase );
    RUN_TEST_CASE( Onboarding_Unit_Serializer, TestOnboardDeviceSerializationNominalCase );
    RUN_TEST_CASE( Onboarding_Unit_Serializer, TestOnboardDeviceSerializationWithoutParameters );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that the serializer for GetDeviceCredentials API generates the expected encoding for an "{}" empty
 * payload.
 */
TEST( Onboarding_Unit_Serializer, TestGetDeviceCredentialsSerializationNominalCase )
{
    IotSerializerEncoderObject_t testEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;

    /* The request payload is an empty map container that needs. */
    const uint8_t pExpectedSerialization[] =
    {
        0xA0 /*# map( 0 ) */
    };

    uint8_t pSerializationBuffer[ sizeof( pExpectedSerialization ) ] = { 0 };

    /* Test the serializer function without a valid buffer. */
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS,
                       _AwsIotOnboarding_SerializeGetDeviceCredentialsRequestPayload( &testEncoder,
                                                                                      NULL,
                                                                                      0 ) );
    TEST_ASSERT_EQUAL( sizeof( pExpectedSerialization ),
                       _pAwsIotOnboardingEncoder->getExtraBufferSizeNeeded( &testEncoder ) );
    _pAwsIotOnboardingEncoder->destroy( &testEncoder );


    /* Test the serializer function without a valid buffer. */
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS,
                       _AwsIotOnboarding_SerializeGetDeviceCredentialsRequestPayload( &testEncoder,
                                                                                      pSerializationBuffer,
                                                                                      sizeof( pSerializationBuffer ) ) );

    _pAwsIotOnboardingEncoder->destroy( &testEncoder );

    /* Make sure that the serializer function generated the expected payload. */
    TEST_ASSERT_EQUAL( 0, memcmp( pExpectedSerialization, pSerializationBuffer,
                                  sizeof( pExpectedSerialization ) ) );
}

/**
 * @brief Tests the behavior of the serializer for generating a payload containing ONLY the "certificate" data.
 */
TEST( Onboarding_Unit_Serializer, TestOnboardDeviceSerializationNominalCase )
{
    AwsIotOnboardingOnboardDeviceRequestInfo_t testRequestInfo;

    testRequestInfo.pDeviceCertificateId = _testCertificateId;
    testRequestInfo.deviceCertificateIdLength = strlen( _testCertificateId );
    testRequestInfo.pParametersStart = _sampleParameters;
    testRequestInfo.numOfParameters = _numOfSampleParameters;

    IotSerializerEncoderObject_t testEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;

    /**
     * @brief The expected serialized payload for OnboardDevice API request containing #_sampleParameters and
     * #_testCertificateId.
     */
    static const uint8_t pExpectedSerialization[] =
    {
        /* *INDENT-OFF* */
        0xA2,                                                                                                 /*# map( 2 ) */
        0x6D,                                                                                                 /*# text( 13 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64,                         /*# "certificateId" */
        0x71,                                                                                                 /*# text( 17 ) */
        0x54, 0x65, 0x73, 0x74, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64, /*# "TestCertificateId" */
        0x6A,                                                                                                 /*# text( 10 ) */
        0x70, 0x61, 0x72, 0x61, 0x6D, 0x65, 0x74, 0x65, 0x72, 0x73,                                           /*# "parameters" */
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

    uint8_t pSerializationBuffer[ sizeof( pExpectedSerialization ) ] = { 0 };

    /* Test the serializer function without a valid buffer. */
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS,
                       _AwsIotOnboarding_SerializeOnboardDeviceRequestPayload( &testRequestInfo,
                                                                               &testEncoder,
                                                                               NULL,
                                                                               0 ) );
    TEST_ASSERT_EQUAL( sizeof( pExpectedSerialization ),
                       _pAwsIotOnboardingEncoder->getExtraBufferSizeNeeded( &testEncoder ) );
    _pAwsIotOnboardingEncoder->destroy( &testEncoder );

    /* Test the serializer function with a valid buffer. */
    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS,
                       _AwsIotOnboarding_SerializeOnboardDeviceRequestPayload( &testRequestInfo,
                                                                               &testEncoder,
                                                                               pSerializationBuffer,
                                                                               sizeof( pSerializationBuffer ) ) );

    _pAwsIotOnboardingEncoder->destroy( &testEncoder );

    /* Make sure that the serializer generated the expected request payload data. */
    TEST_ASSERT_EQUAL( 0, memcmp( pExpectedSerialization, pSerializationBuffer,
                                  sizeof( pExpectedSerialization ) ) );
}

/**
 * @brief Tests the behavior of the serializer for generating a payload containing "certificate" and "parameters".
 */
TEST( Onboarding_Unit_Serializer, TestOnboardDeviceSerializationWithoutParameters )
{
    AwsIotOnboardingOnboardDeviceRequestInfo_t testRequestInfo;

    testRequestInfo.pDeviceCertificateId = _testCertificateId;
    testRequestInfo.deviceCertificateIdLength = strlen( _testCertificateId );
    testRequestInfo.pParametersStart = NULL;
    testRequestInfo.numOfParameters = 0;

    IotSerializerEncoderObject_t testEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;

    /**
     * @brief The expected serialized payload for OnboardDevice API request containing #_sampleParameters and
     * #_testCertificateId.
     */
    static const uint8_t pExpectedSerializationWithoutParameters[] =
    {
        /* *INDENT-OFF* */
        0xA1,                                                                                                 /*# map( 2 ) */
        0x6D,                                                                                                 /*# text( 13 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64,                         /*# "certificateId" */
        0x71,                                                                                                 /*# text( 17 ) */
        0x54, 0x65, 0x73, 0x74, 0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64, /*# "TestCertificateId" */
        /* *INDENT-ON* */
    };

    uint8_t pSerializationBuffer[ sizeof( pExpectedSerializationWithoutParameters ) ] = { 0 };

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS,
                       _AwsIotOnboarding_SerializeOnboardDeviceRequestPayload( &testRequestInfo,
                                                                               &testEncoder,
                                                                               pSerializationBuffer,
                                                                               sizeof( pSerializationBuffer ) ) );

    _pAwsIotOnboardingEncoder->destroy( &testEncoder );

    /* Make sure that the serializer generated the expected request payload data. */
    TEST_ASSERT_EQUAL( 0, memcmp( pExpectedSerializationWithoutParameters, pSerializationBuffer,
                                  sizeof( pExpectedSerializationWithoutParameters ) ) );
}
