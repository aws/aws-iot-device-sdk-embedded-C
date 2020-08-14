#include <string.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "json.h"

/* Sample test from the docs. */
#define JSON_QUERY_SEPARATOR              '.'

#define SAMPLE_JSON                                                                  \
    "{\"literal\":true, \"more_literals\": {\"literal2\":false, \"literal3\":null}," \
    "\"exp1\": 5E+3, \"more_exponents\": [5e+2, 4e-2, 93E-5, 128E-6],  "             \
    "\"number\": 123412, "                                                           \
    "\"decimal\":109238.42091289, "                                                  \
    "\"foo\":\"abc\",\"bar\":{\"foo\":\"xyz\"}}"
#define SAMPLE_JSON_LEN                   ( sizeof( SAMPLE_JSON ) - 1 )

#define SAMPLE_JSON_QUERY_KEY             "bar.foo"
#define SAMPLE_JSON_QUERY_KEY_LEN         ( sizeof( SAMPLE_JSON_QUERY_KEY ) - 1 )

#define JSON_EXPECTED_QUERY_ANSWER        "xyz"
#define JSON_EXPECTED_QUERY_ANSWER_LEN    ( sizeof( JSON_EXPECTED_QUERY_ANSWER ) - 1 )

#define SAMPLE_JSON_TRAILING_COMMA        "{\"foo\":\"abc\",\"bar\":{\"foo\" : \"xyz\",}}"
#define SAMPLE_JSON_TRAILING_COMMA_LEN    ( sizeof( SAMPLE_JSON_TRAILING_COMMA ) - 1 )

#define SAMPLE_JSON_TRAILING_SPACE                                                   \
    "{\"literal\":true, \"more_literals\": {\"literal2\":false, \"literal3\":null}," \
    "\"exp1\": 5E+3, \"more_exponents\": [5e+2, 4e-2, 93E-5, 128E-6],  "             \
    "\"number\": 123412, "                                                           \
    "\"decimal\":109238.42091289, "                                                  \
    "\"foo\":\"abc\",\"bar\":{\"foo\":\"xyz\"}} "

/* We use sizeof( SAMPLE_JSON ) here because the trailing space must not be
 * included in the length of the string. */
#define SAMPLE_JSON_TRAILING_SPACE_LEN    ( sizeof( SAMPLE_JSON ) - 1 )

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

/* ========================================================================== */

/**
 * @brief Test that JSON_Validate is able to classify valid JSON correctly.
 */
void test_JSON_Validate_Valid_JSON( void )
{
    JSONStatus_t jsonStatus;

    jsonStatus = JSON_Validate( SAMPLE_JSON, SAMPLE_JSON_LEN );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );
}

/**
 * @brief Test that JSON_Validate is able to classify invalid JSON correctly.
 */
void test_JSON_Validate_Invalid_JSON( void )
{
    JSONStatus_t jsonStatus;

    jsonStatus = JSON_Validate( SAMPLE_JSON_TRAILING_COMMA,
                                SAMPLE_JSON_TRAILING_COMMA_LEN );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( SAMPLE_JSON_TRAILING_SPACE,
                                SAMPLE_JSON_TRAILING_SPACE_LEN );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );
}

/**
 * @brief Test that JSON_Search is able to classify invalid JSON correctly.
 */
void test_JSON_Search_Valid_JSON( void )
{
    JSONStatus_t jsonStatus;
    char * outValue;
    size_t outValueLength;

    jsonStatus = JSON_Search( SAMPLE_JSON,
                              SAMPLE_JSON_LEN,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );

    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );
    TEST_ASSERT_EQUAL( outValueLength, JSON_EXPECTED_QUERY_ANSWER_LEN );
    TEST_ASSERT_EQUAL_STRING_LEN( JSON_EXPECTED_QUERY_ANSWER, outValue, outValueLength );
}
