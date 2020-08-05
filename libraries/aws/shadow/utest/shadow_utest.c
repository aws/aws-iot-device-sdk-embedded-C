/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 *
 */

/**
 * @file shadow_utest.c
 * @brief Tests for the user-facing API functions (declared in shadow.h).
 */

/* Standard includes. */
#include <stdint.h>
#include <string.h>

/* Test framework includes. */
#include "unity.h"

/* Shadow include. */
#include "shadow.h"


/*-----------------------------------------------------------*/

/**
 * @brief The Thing Name shared among all the tests.
 */
#define TEST_THING_NAME                                      "TestThingName"

/**
 * @brief The length of #TEST_THING_NAME.
 */
#define TEST_THING_NAME_LENGTH                               ( sizeof( TEST_THING_NAME ) - 1 )

/**
 * @brief The shadow topic string "update" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_UPDATE                      "$aws/things/TestThingName/shadow/update"

/**
 * @brief The shadow topic string "update/accepted" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED             "$aws/things/TestThingName/shadow/update/accepted"

/**
 * @brief The shadow topic string "update/rejected" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_UPDATE_REJECTED             "$aws/things/TestThingName/shadow/update/rejected"

/**
 * @brief The shadow topic string "update/documents" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS            "$aws/things/TestThingName/shadow/update/documents"

/**
 * @brief The shadow topic string "update/delta" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_UPDATE_DELTA                "$aws/things/TestThingName/shadow/update/delta"

/**
 * @brief The shadow topic string "get" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_GET                         "$aws/things/TestThingName/shadow/get"

/**
 * @brief The shadow topic string "get/accepted" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED                "$aws/things/TestThingName/shadow/get/accepted"

/**
 * @brief The shadow topic string "get/rejected" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_GET_REJECTED                "$aws/things/TestThingName/shadow/get/rejected"

/**
 * @brief The shadow topic string "delete" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_DELETE                      "$aws/things/TestThingName/shadow/delete"

/**
 * @brief The shadow topic string "delete/accepted" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_DELETE_ACCEPTED             "$aws/things/TestThingName/shadow/delete/accepted"

/**
 * @brief The shadow topic string "delete/rejected" shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_STRING_DELETE_REJECTED             "$aws/things/TestThingName/shadow/delete/rejected"

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_UPDATE shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_UPDATE                      ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_UPDATE ) - 1U  )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED             ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED ) - 1U  )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_UPDATE_REJECTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_UPDATE_REJECTED             ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_UPDATE_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS            ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_UPDATE_DELTA shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_UPDATE_DELTA                ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_UPDATE_DELTA ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_GET shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_GET                         ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_GET ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED                ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_GET_REJECTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_GET_REJECTED                ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_GET_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_DELETE shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_DELETE                      ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_DELETE ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_DELETE_ACCEPTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED             ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_DELETE_ACCEPTED ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_DELETE_REJECTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_DELETE_REJECTED             ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_DELETE_REJECTED ) - 1U )

/**
 * @brief A topic string with an empty thing name.
 */
#define TEST_SHADOW_TOPIC_STRING_EMPTY_THINGNAME             "$aws/things/"

/**
 * @brief A topic string with an empty shadow message type.
 */
#define TEST_SHADOW_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE   "$aws/things/TestThingName"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE     "$aws/things/TestThingName/shadow/invalid/invalid"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_SHADOW_TOPIC_STRING_INVALID_GET_REJECTED        "$aws/things/TestThingName/shadow/get/rejected/gibberish"

/**
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_SHADOW_TOPIC_STRING_INVALID_PREFIX              "$aws/jobs/TestThingName/shadow/get/rejected"

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_EMPTY_THINGNAME shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_EMPTY_THINGNAME             ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_EMPTY_THINGNAME ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_EMPTY_SHADOW_MESSAGE_TYPE   ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE     ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_INVALID_GET_REJECTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_INVALID_GET_REJECTED        ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_INVALID_GET_REJECTED ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_INVALID_PREFIX shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_INVALID_PREFIX              ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_STRING_INVALID_PREFIX ) - 1U )

/**
 * @brief The init value for a topic buffer.
 */
#define TEST_SHADOW_TOPIC_BUFFER_INITIALZIE                  "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456789abcdefghijklmno"

/**
 * @brief The init value for a topic buffer.
 */
#define TEST_SHADOW_TOPIC_BUFFER_MODIFIED                    "$aws/things/TestThingName/shadow/get/acceptedklmno"

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_DELETE_REJECTED shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_BUFFER_LENGTH                      ( ( uint16_t ) sizeof( TEST_SHADOW_TOPIC_BUFFER_INITIALZIE )  - 1U )

/*-----------------------------------------------------------*/

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}
/*-----------------------------------------------------------*/

/**
 * @brief Tests the macros generates the expected strings.
 */
void test_Shadow_MacrosString( void )
{
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_UPDATE, SHADOW_TOPIC_STRING_UPDATE( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED, SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_UPDATE_REJECTED, SHADOW_TOPIC_STRING_UPDATE_REJECTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS, SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_UPDATE_DELTA, SHADOW_TOPIC_STRING_UPDATE_DELTA( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_GET, SHADOW_TOPIC_STRING_GET( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED, SHADOW_TOPIC_STRING_GET_ACCEPTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_GET_REJECTED, SHADOW_TOPIC_STRING_GET_REJECTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_DELETE, SHADOW_TOPIC_STRING_DELETE( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_DELETE_ACCEPTED, SHADOW_TOPIC_STRING_DELETE_ACCEPTED( TEST_THING_NAME ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_STRING_DELETE_REJECTED, SHADOW_TOPIC_STRING_DELETE_REJECTED( TEST_THING_NAME ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the macros generates the expected strings length.
 */
void test_Shadow_MacrosLength( void )
{
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_UPDATE, SHADOW_TOPIC_LENGTH_UPDATE( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED, SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_UPDATE_REJECTED, SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS, SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_UPDATE_DELTA, SHADOW_TOPIC_LENGTH_UPDATE_DELTA( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_GET, SHADOW_TOPIC_LENGTH_GET( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED, SHADOW_TOPIC_LENGTH_GET_ACCEPTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_GET_REJECTED, SHADOW_TOPIC_LENGTH_GET_REJECTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_DELETE, SHADOW_TOPIC_LENGTH_DELETE( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED, SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED( TEST_THING_NAME_LENGTH ) );
    TEST_ASSERT_EQUAL( TEST_SHADOW_TOPIC_LENGTH_DELETE_REJECTED, SHADOW_TOPIC_LENGTH_DELETE_REJECTED( TEST_THING_NAME_LENGTH ) );
}
/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_GetTopicString() with an invalid
 *        document info parameter.
 */
void test_Shaodw_GetTopicString_Invalid_Parameters( void )
{
    ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;
    uint16_t outLength = 0;
    ShadowTopicStringType_t topicType = ShadowTopicStringTypeGetAccepted;
    char topicBuffer[ TEST_SHADOW_TOPIC_BUFFER_LENGTH ] = TEST_SHADOW_TOPIC_BUFFER_INITIALZIE;
    uint16_t bufferSize = TEST_SHADOW_TOPIC_BUFFER_LENGTH;
    char topicBufferGetAccepted[ SHADOW_TOPIC_LENGTH_GET_ACCEPTED( TEST_THING_NAME_LENGTH ) ] = { 0 };
    uint16_t bufferSizeGetAccepted = TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED;

    /* Call Shadow_GetTopicString() with various combinations of
     * incorrect paramters. */
    shadowStatus = Shadow_GetTopicString( 0,
                                          "",
                                          0,
                                          & ( topicBuffer[ 0 ] ),
                                          bufferSize,
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_GetTopicString( topicType,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          NULL,
                                          0,
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_GetTopicString( ShadowTopicStringTypeMaxNum + 1,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          & ( topicBuffer[ 0 ] ),
                                          bufferSize,
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_GetTopicString( topicType,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          & ( topicBuffer[ 0 ] ),
                                          bufferSize,
                                          NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_GetTopicString( topicType,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          & ( topicBuffer[ 0 ] ),
                                          0,
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BUFFER_TOO_SMALL, shadowStatus );

    shadowStatus = Shadow_GetTopicString( topicType,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          & ( topicBuffer[ 0 ] ),
                                          ( bufferSize / 2 ),
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BUFFER_TOO_SMALL, shadowStatus );

    /* Call Shadow_GetTopicString() with valid parameters but bufferSize > topic string length
     * and verify result. */
    shadowStatus = Shadow_GetTopicString( topicType,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          & ( topicBuffer[ 0 ] ),
                                          bufferSize,
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_LESS_THAN( bufferSize, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_TOPIC_BUFFER_MODIFIED,
                                  topicBuffer,
                                  bufferSize );

    /* Call Shadow_GetTopicString() with valid parameters and verify result. */
    shadowStatus = Shadow_GetTopicString( topicType,
                                          TEST_THING_NAME,
                                          TEST_THING_NAME_LENGTH,
                                          & ( topicBufferGetAccepted[ 0 ] ),
                                          bufferSizeGetAccepted,
                                          & outLength );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED, outLength );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED,
                                  topicBufferGetAccepted,
                                  bufferSizeGetAccepted );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_MatchTopic() with various
 *        invalid parameters.
 */
void test_Shadow_MatchTopic_Invalid_Parameters( void )
{
    ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint16_t thingNameLength = 0;
    const char topicBuffer[ TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED ] = TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED;
    uint16_t bufferSize = TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED;

    /* Call Shadow_MatchTopic() with various combinations of
     * incorrect parameters. */
    shadowStatus = Shadow_MatchTopic( NULL,
                                      bufferSize,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopic( & ( topicBuffer[ 0 ] ),
                                      0,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopic( & ( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      NULL,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopic( & ( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      & messageType,
                                      & pThingName,
                                      NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, shadowStatus );

    shadowStatus = Shadow_MatchTopic( TEST_SHADOW_TOPIC_STRING_INVALID_PREFIX,
                                      TEST_SHADOW_TOPIC_LENGTH_INVALID_PREFIX,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, shadowStatus );

    shadowStatus = Shadow_MatchTopic( TEST_SHADOW_TOPIC_STRING_EMPTY_THINGNAME,
                                      TEST_SHADOW_TOPIC_LENGTH_EMPTY_THINGNAME,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_THINGNAME_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopic( TEST_SHADOW_TOPIC_STRING_EMPTY_SHADOW_MESSAGE_TYPE,
                                      TEST_SHADOW_TOPIC_LENGTH_EMPTY_SHADOW_MESSAGE_TYPE,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopic( TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE,
                                      TEST_SHADOW_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, shadowStatus );

    shadowStatus = Shadow_MatchTopic( TEST_SHADOW_TOPIC_STRING_INVALID_GET_REJECTED,
                                      TEST_SHADOW_TOPIC_LENGTH_INVALID_GET_REJECTED,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, shadowStatus );

    shadowStatus = Shadow_MatchTopic( & ( topicBuffer[ 0 ] ),
                                      bufferSize / 2,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_SHADOW_MESSAGE_TYPE_PARSE_FAILED, shadowStatus );

    shadowStatus = Shadow_MatchTopic( & ( topicBuffer[ 0 ] ),
                                      bufferSize * 2,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, shadowStatus );

    /* Call Shadow_MatchTopic() with valid paramters and verify result. */
    shadowStatus = Shadow_MatchTopic( & ( topicBuffer[ 0 ] ),
                                      bufferSize,
                                      & messageType,
                                      & pThingName,
                                      & thingNameLength );

    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_SUCCESS, shadowStatus );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, pThingName, TEST_THING_NAME_LENGTH );
}


/*-----------------------------------------------------------*/
