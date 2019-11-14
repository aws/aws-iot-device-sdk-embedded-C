/*
 * AWS IoT Common V1.0.0
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
 * @file aws_iot_tests_doc_parser.c
 * @brief Tests for the AWS IoT Parser.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

/* AWS IoT parser include. */
#include "aws_iot_doc_parser.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Wrapper for parsing AWS IoT JSON documents and checking the result.
 */
static void _parseJson( bool expectedResult,
                        const char * pJsonDocument,
                        size_t jsonDocumentLength,
                        const char * pJsonKey,
                        const char * pExpectedJsonValue,
                        size_t expectedJsonValueLength )
{
    const char * pJsonValue = NULL;
    size_t jsonValueLength = 0;

    TEST_ASSERT_EQUAL_INT( expectedResult,
                           AwsIotDocParser_FindValue( pJsonDocument,
                                                      jsonDocumentLength,
                                                      pJsonKey,
                                                      strlen( pJsonKey ),
                                                      &pJsonValue,
                                                      &jsonValueLength ) );

    if( expectedResult == true )
    {
        TEST_ASSERT_EQUAL( expectedJsonValueLength, jsonValueLength );
        TEST_ASSERT_EQUAL_STRING_LEN( pExpectedJsonValue, pJsonValue, jsonValueLength );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Shadow parser tests.
 */
TEST_GROUP( Aws_Iot_Doc_Unit_Parser );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Shadow parser tests.
 */
TEST_SETUP( Aws_Iot_Doc_Unit_Parser )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Shadow parser tests.
 */
TEST_TEAR_DOWN( Aws_Iot_Doc_Unit_Parser )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Shadow parser tests.
 */
TEST_GROUP_RUNNER( Aws_Iot_Doc_Unit_Parser )
{
    RUN_TEST_CASE( Aws_Iot_Doc_Unit_Parser, JsonValid );
    RUN_TEST_CASE( Aws_Iot_Doc_Unit_Parser, JsonInvalid );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests parsing valid JSON documents.
 */
TEST( Aws_Iot_Doc_Unit_Parser, JsonValid )
{
    /* Parse JSON document with string, int, bool, and null. */
    {
        const char pJsonDocument[ 82 ] = "{\"name\" \n\r:\n \"John Smith\", \"age\"    :\n\r 30, \n \"isAlive\"  : true, \r \"spouse\":null}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( true, pJsonDocument, jsonDocumentLength, "name", "\"John Smith\"", 12 );
        _parseJson( true, pJsonDocument, jsonDocumentLength, "age", "30", 2 );
        _parseJson( true, pJsonDocument, jsonDocumentLength, "isAlive", "true", 4 );
        _parseJson( true, pJsonDocument, jsonDocumentLength, "spouse", "null", 4 );

        /* Attempt to find a key not in the JSON document. */
        _parseJson( false, pJsonDocument, jsonDocumentLength, "address", NULL, 0 );
    }

    /* Parse JSON document with objects and arrays. */
    {
        const char pJsonDocument[ 91 ] = "{\"object\" : { \"nestedObject\": { \"string\":\"\\\"test\\\"\", \"array\":[[1,2,3],[1,2,3],[1,2,3]]}}}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( true, pJsonDocument, jsonDocumentLength, "object", "{ \"nestedObject\": { \"string\":\"\\\"test\\\"\", \"array\":[[1,2,3],[1,2,3],[1,2,3]]}}", 76 );
        _parseJson( true, pJsonDocument, jsonDocumentLength, "nestedObject", "{ \"string\":\"\\\"test\\\"\", \"array\":[[1,2,3],[1,2,3],[1,2,3]]}", 57 );
        _parseJson( true, pJsonDocument, jsonDocumentLength, "array", "[[1,2,3],[1,2,3],[1,2,3]]", 25 );
    }

    /* JSON document with escape sequences. */
    {
        const char pJsonDocument[ 40 ] = "{\"key\": \"value\", \"ke\\\"y2\": \"\\\"value\\\"\"}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        /* Attempt to find a JSON key that is actually a value. */
        _parseJson( false, pJsonDocument, jsonDocumentLength, "value", NULL, 0 );

        /* Attempt to find a JSON key that is a substring of a key. */
        _parseJson( false, pJsonDocument, jsonDocumentLength, "ke", NULL, 0 );

        /* Find a key and string that contain escaped quotes. */
        _parseJson( true, pJsonDocument, jsonDocumentLength, "ke\\\"y2", "\"\\\"value\\\"\"", 11 );
    }

    /* Short JSON document. */
    {
        const char pJsonDocument[ 16 ] = "{\"key\":\"value\"}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        /* Attempt to find a key longer than the JSON document. */
        _parseJson( false, pJsonDocument, jsonDocumentLength, "longlonglonglongkey", NULL, 0 );
    }

    /* JSON with '{' '}' in value in nested level*/
    {
        const char pJsonDocument[ 42 ] = "{\"key\":{\"key2\":\"{{{{}}\", \"key3\":\"value\"}}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        /* Attempt to find a value which has value a string with '{' '}' */
        _parseJson( true, pJsonDocument, jsonDocumentLength, "key", "{\"key2\":\"{{{{}}\", \"key3\":\"value\"}", 33 );
    }

    /* JSON with objects elements of the array */
    {
        const char pJsonDocument[ 63 ] = "{\"key\":\"value\", \"arr\": [{\"key1\":\"value1\"}, {\"key2\":\"value2\"}]}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        /* Attempt to find a value with objects as members of the array */
        _parseJson( true, pJsonDocument, jsonDocumentLength, "arr", "[{\"key1\":\"value1\"}, {\"key2\":\"value2\"}]", 38 );
    }

    /* JSON with with false in the value */
    {
        const char pJsonDocument[ 33 ] = "{\"key\":\"value\", \"keybool\":false}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        /* Attempt to find a boolean value */
        _parseJson( true, pJsonDocument, jsonDocumentLength, "keybool", "false", 5 );
    }

    /* JSON with with different elements in the array */
    {
        const char pJsonDocument[ 85 ] = "{\"key\":\"value\", \"arr\":[4, \"string\", true, {\"key1\":\"value1\", \"arr1\":[1,2,3]}, 99]}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        /* Attempt to find a value with different elements in the array */
        _parseJson( true, pJsonDocument, jsonDocumentLength, "arr", "[4, \"string\", true, {\"key1\":\"value1\", \"arr1\":[1,2,3]}, 99]", 58 );
    }
}


/*-----------------------------------------------------------*/

/**
 * @brief Tests that parsing invalid JSON documents does not read out-of-bounds
 * memory.
 */
TEST( Aws_Iot_Doc_Unit_Parser, JsonInvalid )
{
    /* JSON key not followed by a : */
    {
        const char pJsonDocument[ 16 ] = "{\"string\"      ";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "string", NULL, 0 );
    }

    /* JSON value not followed by a , */
    {
        const char pJsonDocument[ 30 ] = "{\"int\": 10 \"string\": \"hello\"}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "int", NULL, 0 );
    }

    /* JSON key with no value. */
    {
        const char pJsonDocument[ 18 ] = "{\"string\":       ";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "string", NULL, 0 );
    }

    /* Unterminated JSON primitive. */
    {
        const char pJsonDocument[ 12 ] = "{\"int\":1000";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "int", NULL, 0 );
    }

    /* Unterminated JSON string (ending is an escaped quote). */
    {
        const char pJsonDocument[ 15 ] = "{\"string\": \"\\\"";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "string", NULL, 0 );
    }

    /* Unterminated JSON string (ending is not a quote). */
    {
        const char pJsonDocument[ 15 ] = "{\"string\": \" \\";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "string", NULL, 0 );
    }

    /* Unterminated JSON object. */
    {
        const char pJsonDocument[ 42 ] = "{\"object\": {\"key\": { \"nestedKey\":\"value\"}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "object", NULL, 0 );
    }

    /* Unterminated JSON array. */
    {
        const char pJsonDocument[ 27 ] = "{\"array\": [[1,2,3],[1,2,3]";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( false, pJsonDocument, jsonDocumentLength, "array", NULL, 0 );
    }

    /* Invalid JSON not validated for correctness. Incorrect value. */
    {
        const char pJsonDocument[ 30 ] = "{\"key\": \"value\", \"key2\": {]}}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( true, pJsonDocument, jsonDocumentLength, "key", "\"value\"", 7 );
    }

    /* Invalid JSON not validated for correctness. Incorrect paranthesis. */
    {
        const char pJsonDocument[ 30 ] = "{\"key\": \"value\", \"key2\": {}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( true, pJsonDocument, jsonDocumentLength, "key", "\"value\"", 7 );
    }

    /* Invalid JSON not validated for correctness. Incorrect `,`s. */
    {
        const char pJsonDocument[ 52 ] = "{\"key\": \"value\", \"key2\": \"value1\" \"key3\": \"value3\"}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( true, pJsonDocument, jsonDocumentLength, "key", "\"value\"", 7 );
    }

    /* Invalid JSON not validated for correctness. Incorrect nesting level.
     * Missing `:`.
     */
    {
        const char pJsonDocument[ 43 ] = "{\"key\": \"value\", \"key2\":{\"key3\" \"value3\"}}";
        size_t jsonDocumentLength = strlen( pJsonDocument );

        _parseJson( true, pJsonDocument, jsonDocumentLength, "key", "\"value\"", 7 );
    }
}

/*-----------------------------------------------------------*/
