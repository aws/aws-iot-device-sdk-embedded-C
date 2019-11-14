/*
 * AWS IoT Shadow V2.1.0
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
 * @file aws_iot_tests_shadow_parser.c
 * @brief Tests for the Shadow topic name and JSON parser functions.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

/* Shadow internal include. */
#include "private/aws_iot_shadow_internal.h"

/* Test framework includes. */
#include "unity_fixture.h"

/* SDK initialization include. */
#include "iot_init.h"

/*-----------------------------------------------------------*/

/**
 * @brief The size of the buffers allocated for holding Shadow error documents.
 */
#define ERROR_DOCUMENT_BUFFER_SIZE    ( 128 )

/*-----------------------------------------------------------*/

/**
 * @brief Wrapper for generating and parsing error documents.
 */
static void _generateParseErrorDocument( char * pErrorDocument,
                                         AwsIotShadowError_t expectedCode,
                                         const char * pFormat,
                                         ... )
{
    int errorDocumentLength = 0;
    va_list arguments;

    /* Generate an error document. */
    va_start( arguments, pFormat );
    errorDocumentLength = vsnprintf( pErrorDocument,
                                     ERROR_DOCUMENT_BUFFER_SIZE,
                                     pFormat,
                                     arguments );
    va_end( arguments );

    /* Check for errors from vsnprintf. */
    TEST_ASSERT_GREATER_THAN_INT( 0, errorDocumentLength );
    TEST_ASSERT_LESS_THAN_INT( ERROR_DOCUMENT_BUFFER_SIZE, errorDocumentLength );

    /* Parse the error document and check the result. */
    TEST_ASSERT_EQUAL( expectedCode,
                       _AwsIotShadow_ParseErrorDocument( pErrorDocument,
                                                         ( size_t ) errorDocumentLength ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Wrapper for parsing Shadow Thing Names and checking the result.
 */
static void _parseThingName( const char * pTopicName,
                             bool expectedResult,
                             const char * pExpectedThingName )
{
    bool status = true;
    uint16_t topicNameLength = ( uint16_t ) strlen( pTopicName );
    const char * pThingName = NULL;
    size_t thingNameLength = 0;

    status = AwsIot_ParseThingName( pTopicName,
                                    topicNameLength,
                                    &pThingName,
                                    &thingNameLength );
    TEST_ASSERT_EQUAL( expectedResult, status );

    if( expectedResult == true )
    {
        TEST_ASSERT_EQUAL( strlen( pExpectedThingName ), thingNameLength );
        TEST_ASSERT_EQUAL_STRING_LEN( pExpectedThingName, pThingName, thingNameLength );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Shadow parser tests.
 */
TEST_GROUP( Shadow_Unit_Parser );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Shadow parser tests.
 */
TEST_SETUP( Shadow_Unit_Parser )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the Shadow library. */
    TEST_ASSERT_EQUAL( AWS_IOT_SHADOW_SUCCESS, AwsIotShadow_Init( 0 ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Shadow parser tests.
 */
TEST_TEAR_DOWN( Shadow_Unit_Parser )
{
    /* Clean up the Shadow library. */
    AwsIotShadow_Cleanup();

    /* Clean up SDK. */
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Shadow parser tests.
 */
TEST_GROUP_RUNNER( Shadow_Unit_Parser )
{
    RUN_TEST_CASE( Shadow_Unit_Parser, StatusValid );
    RUN_TEST_CASE( Shadow_Unit_Parser, StatusInvalid );
    RUN_TEST_CASE( Shadow_Unit_Parser, ErrorDocument );
    RUN_TEST_CASE( Shadow_Unit_Parser, ErrorDocumentInvalid );
    RUN_TEST_CASE( Shadow_Unit_Parser, ThingName );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests parsing Shadow status from a valid topic name.
 */
TEST( Shadow_Unit_Parser, StatusValid )
{
    AwsIotStatus_t status = AWS_IOT_UNKNOWN;

    /* Parse "accepted" status. */
    status = AwsIot_ParseStatus( "$aws/things/Test_device/shadow/accepted",
                                 39 );
    TEST_ASSERT_EQUAL( AWS_IOT_ACCEPTED, status );

    /* Parse "rejected" status. */
    status = AwsIot_ParseStatus( "$aws/things/Test_device/shadow/rejected",
                                 39 );
    TEST_ASSERT_EQUAL( AWS_IOT_REJECTED, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests parsing Shadow status from invalid topic names.
 */
TEST( Shadow_Unit_Parser, StatusInvalid )
{
    /* Topic too short. */
    TEST_ASSERT_EQUAL( AWS_IOT_UNKNOWN,
                       AwsIot_ParseStatus( "accepted",
                                           8 ) );

    /* Topic missing last character. */
    TEST_ASSERT_EQUAL( AWS_IOT_UNKNOWN,
                       AwsIot_ParseStatus( "$aws/things/Test_device/shadow/accepte",
                                           38 ) );

    /* Topic missing level separator. */
    TEST_ASSERT_EQUAL( AWS_IOT_UNKNOWN,
                       AwsIot_ParseStatus( "$aws/things/Test_device/shadowaccepted",
                                           38 ) );

    /* Topic suffix isn't "accepted" or "rejected". */
    TEST_ASSERT_EQUAL( AWS_IOT_UNKNOWN,
                       AwsIot_ParseStatus( "$aws/things/Test_device/shadow/unknown",
                                           38 ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests parsing valid Shadow error documents.
 */
TEST( Shadow_Unit_Parser, ErrorDocument )
{
    size_t i = 0;
    char pErrorDocument[ ERROR_DOCUMENT_BUFFER_SIZE ] = { 0 };
    AwsIotShadowError_t pValidErrorCodes[] =
    {
        AWS_IOT_SHADOW_BAD_REQUEST,
        AWS_IOT_SHADOW_UNAUTHORIZED,
        AWS_IOT_SHADOW_FORBIDDEN,
        AWS_IOT_SHADOW_NOT_FOUND,
        AWS_IOT_SHADOW_CONFLICT,
        AWS_IOT_SHADOW_TOO_LARGE,
        AWS_IOT_SHADOW_UNSUPPORTED,
        AWS_IOT_SHADOW_TOO_MANY_REQUESTS,
        AWS_IOT_SHADOW_SERVER_ERROR
    };

    /* Generate an error document for every valid error code and parse it. */
    for( i = 0; i < ( sizeof( pValidErrorCodes ) / sizeof( pValidErrorCodes[ 0 ] ) ); i++ )
    {
        _generateParseErrorDocument( pErrorDocument,
                                     pValidErrorCodes[ i ],
                                     "{\"code\": %d, \"message\": \"%s\"}",
                                     ( int ) pValidErrorCodes[ i ],
                                     "Test" );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests parsing invalid Shadow error documents.
 */
TEST( Shadow_Unit_Parser, ErrorDocumentInvalid )
{
    char pErrorDocument[ ERROR_DOCUMENT_BUFFER_SIZE ] = { 0 };

    /* Parse an error document with an unknown code. */
    _generateParseErrorDocument( pErrorDocument,
                                 AWS_IOT_SHADOW_BAD_RESPONSE,
                                 "{\"code\": %d, \"message\": \"%s\"}",
                                 -1,
                                 "Test" );

    /* Parse an error document missing the "code" key. */
    _generateParseErrorDocument( pErrorDocument,
                                 AWS_IOT_SHADOW_BAD_RESPONSE,
                                 "{\"message\": \"Test\"}" );

    /* Parse an error document missing the "message" key. */
    _generateParseErrorDocument( pErrorDocument,
                                 AWS_IOT_SHADOW_BAD_RESPONSE,
                                 "{\"code\": 400}" );

    /* Parse a malformed error document where the code is unterminated. */
    _generateParseErrorDocument( pErrorDocument,
                                 AWS_IOT_SHADOW_BAD_RESPONSE,
                                 "{\"code\": 400" );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests parsing both valid and invalid Shadow topics.
 */
TEST( Shadow_Unit_Parser, ThingName )
{
    /* Valid operation topic. */
    _parseThingName( "$aws/things/TEST/shadow/get/accepted",
                     true,
                     "TEST" );

    /* Valid callback topic. */
    _parseThingName( "$aws/things/TEST/shadow/update/delta",
                     true,
                     "TEST" );

    /* Topic too short. */
    _parseThingName( "$aws/things/TEST/",
                     false,
                     "TEST" );

    /* Incorrect prefix. */
    _parseThingName( "$awsshadow/TEST/shadow/update/accepted",
                     false,
                     "TEST" );

    /* Thing Name unterminated. */
    _parseThingName( "$aws/things/TESTTESTTESTTESTTESTTEST",
                     false,
                     "TESTTESTTESTTESTTESTTEST" );
}

/*-----------------------------------------------------------*/
