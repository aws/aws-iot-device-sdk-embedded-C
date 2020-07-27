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
 * @brief A topic string that is not related to Shadow.
 */
#define TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE     "$aws/things/TestThingName/shadow/invalid/invalid"

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_EMPTY_THINGNAME shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_EMPTY_THINGNAME             ( ( uint16_t ) sizeof( "$aws/things/" ) - 1U )

/**
 * @brief The length of #TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE shared among all test cases.
 */
#define TEST_SHADOW_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE     ( ( uint16_t ) sizeof( "$aws/things/TestThingName/shadow/invalid/invalid" ) - 1U )

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
    /* Empty else MISRA 15.7. */
}

/* Called after each test method. */
void tearDown()
{
    /* Empty else MISRA 15.7. */
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
    /* Empty else MISRA 15.7. */
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
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_UPDATE( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_UPDATE );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_UPDATE_REJECTED( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_UPDATE_REJECTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_UPDATE_DELTA( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_UPDATE_DELTA );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_GET( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_GET );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_GET_ACCEPTED( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_GET_REJECTED( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_GET_REJECTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_DELETE( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_DELETE );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_DELETE_ACCEPTED( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_DELETE_ACCEPTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_STRING_DELETE_REJECTED( TEST_THING_NAME ), TEST_SHADOW_TOPIC_STRING_DELETE_REJECTED );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the macros generates the expected strings length.
 */
void test_Shadow_MacrosLength( void )
{
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_UPDATE( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_UPDATE );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_UPDATE_REJECTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_UPDATE_DELTA( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_UPDATE_DELTA );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_GET( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_GET );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_GET_ACCEPTED( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_GET_REJECTED( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_GET_REJECTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_DELETE( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_DELETE );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED );
    TEST_ASSERT_EQUAL( SHADOW_TOPIC_LENGTH_DELETE_REJECTED( TEST_THING_NAME_LENGTH ), TEST_SHADOW_TOPIC_LENGTH_DELETE_REJECTED );
}
/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_GetTopicString() with an invalid
 *        document info parameter.
 */
void test_Shaodw_GetTopicString_Invalid_Parameters( void )
{
    int16_t ret = 0;
    ShadowTopicStringType_t topicType = SHADOW_TOPIC_STRING_TYPE_GET_ACCEPTED;
    uint8_t  topicBuffer[ TEST_SHADOW_TOPIC_BUFFER_LENGTH ] = TEST_SHADOW_TOPIC_BUFFER_INITIALZIE;
    uint16_t bufferSize = TEST_SHADOW_TOPIC_BUFFER_LENGTH;
    uint8_t  topicBufferGetAccepted[ SHADOW_TOPIC_LENGTH_GET_ACCEPTED( TEST_THING_NAME_LENGTH ) ] = { 0 };
    uint16_t bufferSizeGetAccepted = TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED;

    /* Call Shadow_GetTopicString() with various combinations of
     * incorrect paramters. */
    ret = Shadow_GetTopicString( 0,
                                 "",
                                 0,
                                 & topicBuffer,
                                 bufferSize );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, ret );

    ret = Shadow_GetTopicString( topicType,
                                 TEST_THING_NAME,
                                 TEST_THING_NAME_LENGTH,
                                 NULL,
                                 0 );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, ret );

    ret = Shadow_GetTopicString(SHADOW_TOPIC_STRING_TYPE_MAX_NUM + 1,
                                 TEST_THING_NAME,
                                 TEST_THING_NAME_LENGTH,
                                 & topicBuffer,
                                 bufferSize );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, ret );

    ret = Shadow_GetTopicString( topicType,
                                 TEST_THING_NAME,
                                 TEST_THING_NAME_LENGTH,
                                 & topicBuffer,
                                 0 );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_INVALID_BUFFER_LENGTH, ret );

    ret = Shadow_GetTopicString( topicType,
                                 TEST_THING_NAME,
                                 TEST_THING_NAME_LENGTH,
                                 & topicBuffer,
                                 ( bufferSize / 2 ) );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_INVALID_BUFFER_LENGTH, ret );

    /* Call Shadow_GetTopicString() with valid paramters but bufferSize > topic string length
     * and verify result. */
    ret = Shadow_GetTopicString( topicType,
                                 TEST_THING_NAME,
                                 TEST_THING_NAME_LENGTH,
                                 & topicBuffer,
                                 bufferSize );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED, ret );
    TEST_ASSERT_LESS_THAN( bufferSize, ret );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_TOPIC_BUFFER_MODIFIED,
                                  topicBuffer,
                                  bufferSize );

    /* Call Shadow_GetTopicString() with valid paramters and verify result. */
    ret = Shadow_GetTopicString( topicType,
                                 TEST_THING_NAME,
                                 TEST_THING_NAME_LENGTH,
                                 & topicBufferGetAccepted,
                                 bufferSizeGetAccepted );
    TEST_ASSERT_EQUAL_INT( TEST_SHADOW_TOPIC_LENGTH_GET_ACCEPTED, ret );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_SHADOW_TOPIC_STRING_GET_ACCEPTED,
                                  topicBufferGetAccepted,
                                  bufferSizeGetAccepted );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of Shadow_ValidateTopic() with various
 *        invalid parameters.
 */
void test_Shadow_ValidateTopic_Invalid_Parameters( void )
{
    int16_t ret = 0;
    ShadowMessageInfo_t mMsgInfo = { .thingNameLength = 0 };
    const char topicBuffer[ TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED ] = TEST_SHADOW_TOPIC_STRING_UPDATE_ACCEPTED;
    uint16_t bufferSize = TEST_SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED;

    /* Call Shadow_ValidateTopic() with various combinations of
     * incorrect paramters. */
    ret = Shadow_ValidateTopic( NULL,
                                bufferSize,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, ret );

    ret = Shadow_ValidateTopic( & topicBuffer,
                                0,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, ret );

    ret = Shadow_ValidateTopic( & topicBuffer,
                                bufferSize,
                                NULL );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_BAD_PARAMETER, ret );

    ret = Shadow_ValidateTopic( TEST_SHADOW_TOPIC_STRING_EMPTY_THINGNAME,
                                TEST_SHADOW_TOPIC_LENGTH_EMPTY_THINGNAME,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_THINGNAME_PARSE_FAILED, ret );

    ret = Shadow_ValidateTopic( TEST_SHADOW_TOPIC_STRING_INVALID_SHADOW_RESPONSE,
                                TEST_SHADOW_TOPIC_LENGTH_INVALID_SHADOW_RESPONSE,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, ret );

    ret = Shadow_ValidateTopic( & topicBuffer,
                                bufferSize / 2,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, ret );

    ret = Shadow_ValidateTopic( & topicBuffer,
                                bufferSize * 2,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_FAIL, ret );

    /* Call Shadow_ValidateTopic() with valid paramters and verify result. */
    ret = Shadow_ValidateTopic( & topicBuffer,
                                bufferSize,
                                & mMsgInfo );
    TEST_ASSERT_EQUAL_INT( SHADOW_STATUS_SUCCESS, ret );
    TEST_ASSERT_EQUAL_INT( TEST_THING_NAME_LENGTH, mMsgInfo.thingNameLength );
    TEST_ASSERT_EQUAL_INT( ShadowMessageTypeUpdateAccepted, mMsgInfo.messageType );
    TEST_ASSERT_EQUAL_STRING_LEN( TEST_THING_NAME, mMsgInfo.pThingName, TEST_THING_NAME_LENGTH );
}


/*-----------------------------------------------------------*/
