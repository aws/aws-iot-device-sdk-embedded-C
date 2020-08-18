#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "json.h"


/* Sample test from the docs. */
#define JSON_QUERY_SEPARATOR                         '.'

#define SAMPLE_JSON                                                                  \
    "{\"literal\":true, \"more_literals\": {\"literal2\":false, \"literal3\":null}," \
    "\"exp1\": 5E+3, \"more_exponents\": [5e+2, 4e-2, 93E-5, 128E-6],  "             \
    "\"number\": -123412, "                                                          \
    "\"decimal\":109238.42091289, "                                                  \
    "\"foo\":\"abc\",\"bar\":{\"foo\":\"xyz\"}}"
#define SAMPLE_JSON_LEN                              ( sizeof( SAMPLE_JSON ) - 1 )

#define SAMPLE_JSON_QUERY_KEY                        "bar.foo"
#define SAMPLE_JSON_QUERY_KEY_LEN                    ( sizeof( SAMPLE_JSON_QUERY_KEY ) - 1 )

#define JSON_EXPECTED_QUERY_ANSWER                   "xyz"
#define JSON_EXPECTED_QUERY_ANSWER_LEN               ( sizeof( JSON_EXPECTED_QUERY_ANSWER ) - 1 )

#define SINGLE_SCALAR                                "\"4102985123a\""
#define SINGLE_SCALAR_LEN                            ( sizeof( SINGLE_SCALAR ) - 1 )

#define TRAILING_COMMA_AFTER_VALUE                   "{\"foo\":\"abc\",\"bar\":{\"foo\" : \"xyz\",}}"
#define TRAILING_COMMA_AFTER_VALUE_LENGTH            ( sizeof( TRAILING_COMMA_AFTER_VALUE ) - 1 )

#define INCORRECT_OBJECT_SEPARATOR                   "{\"foo\": \"bar\"; \"bar\": \"foo\"}"
#define INCORRECT_OBJECT_SEPARATOR_LENGTH            ( sizeof( INCORRECT_OBJECT_SEPARATOR ) - 1 )

#define SAMPLE_JSON_TRAILING_SPACES                  "{\"foo\":\"abc\",\"bar\":{\"foo\" : \"xyz\"}}  "
#define SAMPLE_JSON_TRAILING_SPACES_LEN              ( sizeof( SAMPLE_JSON_TRAILING_SPACES ) - 1 )

#define SAMPLE_JSON_KEY_CUT                          "{\"foo\":\"abc\",\"bar\":{\""
#define SAMPLE_JSON_KEY_CUT_LEN                      ( sizeof( SAMPLE_JSON_KEY_CUT ) - 1 )

#define MULTIPLE_VALID_ESCAPES                       "\"\\\\ \\\" \\/ \\b \\f \\n \\r \\t \\\x12\" "
#define MULTIPLE_VALID_ESCAPES_LENGTH                ( sizeof( MULTIPLE_VALID_ESCAPES ) - 1 )

#define ILLEGAL_LEADING_ZEROS                        "07"
#define ILLEGAL_LEADING_ZEROS_LENGTH                 ( sizeof( ILLEGAL_LEADING_ZEROS ) - 1 )

#define TRAILING_COMMA_IN_OBJECT                     "[{\"hello\": [\"foo\",]}]"
#define TRAILING_COMMA_IN_OBJECT_LENGTH              ( sizeof( TRAILING_COMMA_IN_OBJECT ) - 1 )

#define CUT_AFTER_COMMA_SEPARATOR                    "{\"hello\": [5,"
#define CUT_AFTER_COMMA_SEPARATOR_LENGTH             ( sizeof( CUT_AFTER_COMMA_SEPARATOR ) - 1 )

#define CLOSING_SQUARE_BRACKET                       "]"
#define CLOSING_SQUARE_BRACKET_LENGTH                ( sizeof( CLOSING_SQUARE_BRACKET ) - 1 )

#define CLOSING_CURLY_BRACKET                        "}"
#define CLOSING_CURLY_BRACKET_LENGTH                 ( sizeof( CLOSING_CURLY_BRACKET ) - 1 )

#define OPENING_CURLY_BRACKET                        "{"
#define OPENING_CURLY_BRACKET_LENGTH                 ( sizeof( OPENING_CURLY_BRACKET ) - 1 )

#define VALID_UTF8                                   "\"\xc2\xa9 \xe2\x98\x95 \xf0\x9f\x98\x80\""
#define VALID_UTF8_LENGTH                            ( sizeof( VALID_UTF8 ) - 1 )

#define INVALID_UTF8_PREMATURE_CUT                   "{\"foo\":\"abc\",\"bar\":{\"\xc2\xa9 "
#define INVALID_UTF8_PREMATURE_CUT_LENGTH            ( sizeof( INVALID_UTF8_PREMATURE_CUT ) - 1 )

#define WRONG_KEY_VALUE_SEPARATOR                    "{\"hello\";\"world\"}"
#define WRONG_KEY_VALUE_SEPARATOR_LENGTH             ( sizeof( WRONG_KEY_VALUE_SEPARATOR ) - 1 )

/* The octet values C0, C1, and F5 to FF are illegal, since C0 and C1
 * would introduce a non-shortest sequence, and F5 or above would
 * introduce a value greater than the last code point, 0x10FFFF. */
#define INVALID_UTF8_NEXT_BYTE                       "\"\xc2\x00\""
#define INVALID_UTF8_NEXT_BYTE_LENGTH                ( sizeof( INVALID_UTF8_NEXT_BYTE ) - 1 )

/* The first byte in a UTF-8 sequence must be greater than C1. */
#define INVALID_UTF8_START_C1                        "\"\xC1\""
#define INVALID_UTF8_START_C1_LENGTH                 ( sizeof( INVALID_UTF8_START_C1 ) - 1 )

/* The first byte in a UTF-8 sequence must be less than F5. */
#define INVALID_UTF8_START_F5                        "\"\xf5\""
#define INVALID_UTF8_START_F5_LENGTH                 ( sizeof( INVALID_UTF8_START_F5 ) - 1 )

/* UTF-8 is illegal if the number of bytes in the sequence is
 * less than what was expected from the first byte. */
#define INVALID_UTF8_CUT                             "\"\xC2"
#define INVALID_UTF8_CUT_LENGTH                      ( sizeof( INVALID_UTF8_CUT ) - 1 )

#define INVALID_UTF8_SURROGATE_RANGE_MIN             "\"\xED\xA0\x80\""
#define INVALID_UTF8_SURROGATE_RANGE_MIN_LENGTH      ( sizeof( INVALID_UTF8_SURROGATE_RANGE_MIN ) - 1 )

#define INVALID_UTF8_SURROGATE_RANGE_MAX             "\"\xED\xBF\xBF\""
#define INVALID_UTF8_SURROGATE_RANGE_MAX_LENGTH      ( sizeof( INVALID_UTF8_SURROGATE_RANGE_MAX ) - 1 )

#define INVALID_UTF8_GT_MIN_CP_THREE_BYTES           "\"\xC2\x80\x80\""
#define INVALID_UTF8_GT_MIN_CP_THREE_BYTES_LENGTH    ( sizeof( INVALID_UTF8_GT_MIN_CP_THREE_BYTES ) - 1 )

#define INVALID_UTF8_GT_MIN_CP_FOUR_BYTES            "\"\xF4\x9F\xBF\xBF\""
#define INVALID_UTF8_GT_MIN_CP_FOUR_BYTES_LENGTH     ( sizeof( INVALID_UTF8_GT_MIN_CP_FOUR_BYTES ) - 1 )

#define INVALID_UTF8_LT_MAX_CP_FOUR_BYTES            "\"\xF0\x80\x80\x80\""
#define INVALID_UTF8_LT_MAX_CP_FOUR_BYTES_LENGTH     ( sizeof( INVALID_UTF8_LT_MAX_CP_FOUR_BYTES ) - 1 )

#define MISSING_ENCLOSING_ARRAY_MARKER               "{\"key\": []]}"
#define MISSING_ENCLOSING_ARRAY_MARKER_LENGTH        ( sizeof( MISSING_ENCLOSING_ARRAY_MARKER ) - 1 )

#define MISSING_ENCLOSING_OBJECT_MARKER              "\"{\"foo\":\"abc\",\"bar\":{{\"hey\": \"yo\"}"
#define MISSING_ENCLOSING_OBJECT_MARKER_LENGTH       ( sizeof( MISSING_ENCLOSING_OBJECT_MARKER ) - 1 )

/* Unicode escape sequences for coverage. */
#define LEGAL_UNICODE_ESCAPE_SURROGATES              "\"\\uD83D\\ude07\""
#define LEGAL_UNICODE_ESCAPE_SURROGATES_LENGTH       ( sizeof( LEGAL_UNICODE_ESCAPE_SURROGATES ) - 1 )

/* The following escapes are considered invalid. */

/* Hex characters must be used for the unicode escape sequence to be valid. */
#define LITERAL_HEX_UNICODE_ESCAPE_SEQUENCE                "\"\\u\xD8\x3D\\u\xde\x07\""
#define LITERAL_HEX_UNICODE_ESCAPE_SEQUENCE_LENGTH         ( sizeof( LITERAL_HEX_UNICODE_ESCAPE_SEQUENCE ) - 1 )

#define PREMATURE_UNICODE_LOW_SURROGATE                    "\"\\ude07\\uD83D\""
#define PREMATURE_UNICODE_LOW_SURROGATE_LENGTH             ( sizeof( PREMATURE_UNICODE_LOW_SURROGATE ) - 1 )

#define UNICODE_VALID_HIGH_NO_LOW_SURROGATE                "\"\\uD83D\""
#define UNICODE_VALID_HIGH_NO_LOW_SURROGATE_LENGTH         ( sizeof( UNICODE_VALID_HIGH_NO_LOW_SURROGATE ) - 1 )

#define UNICODE_VALID_HIGH_INVALID_LOW_SURROGATE           "\"\\uD83D\\uEFFF\""
#define UNICODE_VALID_HIGH_INVALID_LOW_SURROGATE_LENGTH    ( sizeof( UNICODE_VALID_HIGH_INVALID_LOW_SURROGATE ) - 1 )

#define ILLEGAL_UNICODE_HIGH_SURROGATES                    "\"\\uD83D\\uD83D\""
#define ILLEGAL_UNICODE_HIGH_SURROGATES_LENGTH             ( sizeof( ILLEGAL_UNICODE_HIGH_SURROGATES ) - 1 )

#define UNICODE_ESCAPE_SEQUENCES_BMP                       "\"\\uCB00\\uEFFF\""
#define UNICODE_ESCAPE_SEQUENCES_BMP_LENGTH                ( sizeof( UNICODE_ESCAPE_SEQUENCES_BMP ) - 1 )

/* For security, \u0000 is disallowed. */
#define UNICODE_ESCAPE_SEQUENCE_ZERO_CP                    "\"\\u0000\""
#define UNICODE_ESCAPE_SEQUENCE_ZERO_CP_LENGTH             ( sizeof( UNICODE_ESCAPE_SEQUENCE_ZERO_CP ) - 1 )

/* /NUL escape is disallowed. */
#define NUL_ESCAPE                                         "\"\\\x0\""
#define NUL_ESCAPE_LENGTH                                  ( sizeof( NUL_ESCAPE ) - 1 )

#define ESCAPE_CHAR_ALONE                                  "\"\\\""
#define ESCAPE_CHAR_ALONE_LENGTH                           ( sizeof( ESCAPE_CHAR_ALONE ) - 1 )

/* Any escape character less than 0x21 is considered illegal. */
#define UNKNOWN_ESCAPE                                     "\"\\\x20\""
#define UNKNOWN_ESCAPE_LENGTH                              ( sizeof( UNKNOWN_ESCAPE ) - 1 )

/* An unescaped control character is considered invalid. */
#define UNESCAPED_CONTROL_CHAR                             "\"\x15\""
#define UNESCAPED_CONTROL_CHAR_LENGTH                      ( sizeof( UNESCAPED_CONTROL_CHAR ) - 1 )

/* Triggers the case in which *start >= max for skipDigits. */
#define CUT_AFTER_NUMBER                                   "{\"decimal\": 1"
#define CUT_AFTER_NUMBER_LENGTH                            ( sizeof( CUT_AFTER_NUMBER ) - 1 )

/* Triggers the case in which *start >= max for skipDecimals. */
#define CUT_AFTER_DECIMAL_POINT                            "{\"decimal\": 1."
#define CUT_AFTER_DECIMAL_POINT_LENGTH                     ( sizeof( CUT_AFTER_DECIMAL_POINT ) - 1 )

/* Triggers the case in which *start >= max for skipEscape. */
#define ESCAPE_CHAR_ALONE_NOT_ENCLOSED                     "\"\\"
#define ESCAPE_CHAR_ALONE_NOT_ENCLOSED_LENGTH              ( sizeof( ESCAPE_CHAR_ALONE_NOT_ENCLOSED ) - 1 )

/* Triggers the case in which *start >= max for skipExponent. */
#define CUT_AFTER_EXPONENT_MARKER                          "4e"
#define CUT_AFTER_EXPONENT_MARKER_LENGTH                   ( sizeof( CUT_AFTER_EXPONENT_MARKER ) - 1 )

/* Triggers the case in which *start >= max for skipString. */
#define WHITE_SPACE                                        "   "
#define WHITE_SPACE_LENGTH                                 ( sizeof( WHITE_SPACE ) - 1 )

/* Triggers the case in which *start >= max for skipArrayScalars. */
#define CUT_AFTER_ARRAY_START_MARKER                       "{\"hello\": ["
#define CUT_AFTER_ARRAY_START_MARKER_LENGTH                ( sizeof( CUT_AFTER_ARRAY_START_MARKER ) - 1 )

/* Triggers the cases in which *start >= max for skipObjectScalars and nextKeyValuePair. */
#define CUT_AFTER_OBJECT_START_MARKER                      "{\"hello\": {"
#define CUT_AFTER_OBJECT_START_MARKER_LENGTH               ( sizeof( CUT_AFTER_OBJECT_START_MARKER ) - 1 )
#define CUT_AFTER_KEY                                      "{\"hello\""
#define CUT_AFTER_KEY_LENGTH                               ( sizeof( CUT_AFTER_KEY ) - 1 )

/* A non-number after the exponent marker is illegal. */
#define INVALID_EXPONENT                                   "5Ea"
#define INVALID_EXPONENT_LENGTH                            ( sizeof( INVALID_EXPONENT ) - 1 )

/* Illegal scalar entry in the array. */
#define ILLEGAL_SCALAR_IN_ARRAY                            "{\"hello\": [42, world]\""
#define ILLEGAL_SCALAR_IN_ARRAY_LENGTH                     ( sizeof( ILLEGAL_SCALAR_IN_ARRAY ) - 1 )

/* Key must be a string. */
#define ILLEGAL_KEY_NOT_STRING                             "{key: true}"
#define ILLEGAL_KEY_NOT_STRING_LENGTH                      ( sizeof( ILLEGAL_KEY_NOT_STRING ) - 1 )

/* This prefix is used to generate a nested object. */
#define NESTED_OBJECT_PREFIX                               "{\"k\":"
#define NESTED_OBJECT_PREFIX_LENGTH                        ( sizeof( NESTED_OBJECT_PREFIX ) - 1 )

#define NESTED_OBJECT_VALUE                                "\"v\""
#define NESTED_OBJECT_VALUE_LENGTH                         ( sizeof( NESTED_OBJECT_VALUE ) - 1 )

#ifndef JSON_MAX_DEPTH
    #define JSON_MAX_DEPTH                                 32
#endif

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

char * allocateMaxDepthArray( void )
{
    size_t i, len = ( JSON_MAX_DEPTH + 1 ) * 2;
    char * nestedArray;

    nestedArray = malloc( sizeof( char ) * ( len + 1 ) );

    for( i = 0; i < len / 2; i++ )
    {
        nestedArray[ i ] = '[';
        nestedArray[ len - 1 - i ] = ']';
    }

    nestedArray[ len ] = '\0';

    return nestedArray;
}

char * allocateMaxDepthObject( void )
{
    size_t i = 0, len = NESTED_OBJECT_VALUE_LENGTH +
                        ( JSON_MAX_DEPTH + 1 ) * ( NESTED_OBJECT_PREFIX_LENGTH +
                                                   CLOSING_CURLY_BRACKET_LENGTH );
    char * nestedObject, * nestedObjectCur;

    nestedObject = malloc( sizeof( char ) * ( len + 1 ) );
    nestedObjectCur = nestedObject;

    while( i < ( JSON_MAX_DEPTH + 1 ) * NESTED_OBJECT_PREFIX_LENGTH )
    {
        nestedObjectCur = memcpy( nestedObjectCur, NESTED_OBJECT_PREFIX, NESTED_OBJECT_PREFIX_LENGTH );
        i += NESTED_OBJECT_PREFIX_LENGTH;
        nestedObjectCur += NESTED_OBJECT_PREFIX_LENGTH;
    }

    memcpy( nestedObjectCur, NESTED_OBJECT_VALUE, NESTED_OBJECT_VALUE_LENGTH );
    i += NESTED_OBJECT_VALUE_LENGTH;
    nestedObjectCur += NESTED_OBJECT_VALUE_LENGTH;

    while( i < len )
    {
        *( nestedObjectCur++ ) = '}';
        i++;
    }

    nestedObject[ len ] = '\0';

    printf( "%s\n", nestedObject );

    return nestedObject;
}

/**
 * @brief Test that JSON_Validate is able to classify valid JSON correctly.
 */
void test_JSON_Validate_Valid_JSON( void )
{
    JSONStatus_t jsonStatus;

    jsonStatus = JSON_Validate( SAMPLE_JSON, SAMPLE_JSON_LEN );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( SAMPLE_JSON_TRAILING_SPACES,
                                SAMPLE_JSON_TRAILING_SPACES_LEN );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( MULTIPLE_VALID_ESCAPES, MULTIPLE_VALID_ESCAPES_LENGTH );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( VALID_UTF8, VALID_UTF8_LENGTH );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( LEGAL_UNICODE_ESCAPE_SURROGATES,
                                LEGAL_UNICODE_ESCAPE_SURROGATES_LENGTH );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( UNICODE_ESCAPE_SEQUENCES_BMP,
                                UNICODE_ESCAPE_SEQUENCES_BMP_LENGTH );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );
}

/**
 * @brief Test that JSON_Validate is able to classify invalid JSON correctly.
 */
void test_JSON_Validate_Invalid_JSON( void )
{
    JSONStatus_t jsonStatus;

    jsonStatus = JSON_Validate( TRAILING_COMMA_IN_OBJECT,
                                TRAILING_COMMA_IN_OBJECT_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_COMMA_SEPARATOR,
                                CUT_AFTER_COMMA_SEPARATOR_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( TRAILING_COMMA_AFTER_VALUE,
                                TRAILING_COMMA_AFTER_VALUE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( NUL_ESCAPE, NUL_ESCAPE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( UNKNOWN_ESCAPE, UNKNOWN_ESCAPE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( CLOSING_SQUARE_BRACKET,
                                CLOSING_SQUARE_BRACKET_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( CLOSING_CURLY_BRACKET,
                                CLOSING_CURLY_BRACKET_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( ESCAPE_CHAR_ALONE, ESCAPE_CHAR_ALONE_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( WHITE_SPACE, WHITE_SPACE_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_NUMBER,
                                CUT_AFTER_NUMBER_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_ARRAY_START_MARKER,
                                CUT_AFTER_ARRAY_START_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_OBJECT_START_MARKER,
                                CUT_AFTER_OBJECT_START_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_KEY,
                                CUT_AFTER_KEY_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( WRONG_KEY_VALUE_SEPARATOR,
                                WRONG_KEY_VALUE_SEPARATOR_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_EXPONENT_MARKER,
                                CUT_AFTER_EXPONENT_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( MISSING_ENCLOSING_ARRAY_MARKER,
                                MISSING_ENCLOSING_ARRAY_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_EXPONENT,
                                INVALID_EXPONENT_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( CUT_AFTER_DECIMAL_POINT,
                                CUT_AFTER_DECIMAL_POINT_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( ILLEGAL_LEADING_ZEROS,
                                ILLEGAL_LEADING_ZEROS_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( ILLEGAL_SCALAR_IN_ARRAY,
                                ILLEGAL_SCALAR_IN_ARRAY_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( ESCAPE_CHAR_ALONE_NOT_ENCLOSED,
                                ESCAPE_CHAR_ALONE_NOT_ENCLOSED_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( UNESCAPED_CONTROL_CHAR, UNESCAPED_CONTROL_CHAR_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_NEXT_BYTE, INVALID_UTF8_NEXT_BYTE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_START_C1, INVALID_UTF8_START_C1_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_START_F5, INVALID_UTF8_START_F5_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_CUT, INVALID_UTF8_CUT_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_GT_MIN_CP_FOUR_BYTES,
                                INVALID_UTF8_GT_MIN_CP_FOUR_BYTES_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_GT_MIN_CP_THREE_BYTES,
                                INVALID_UTF8_GT_MIN_CP_THREE_BYTES_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_LT_MAX_CP_FOUR_BYTES,
                                INVALID_UTF8_LT_MAX_CP_FOUR_BYTES_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_SURROGATE_RANGE_MIN,
                                INVALID_UTF8_SURROGATE_RANGE_MIN_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_SURROGATE_RANGE_MAX,
                                INVALID_UTF8_SURROGATE_RANGE_MAX_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_UTF8_SURROGATE_RANGE_MAX,
                                INVALID_UTF8_SURROGATE_RANGE_MAX_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( LITERAL_HEX_UNICODE_ESCAPE_SEQUENCE,
                                LITERAL_HEX_UNICODE_ESCAPE_SEQUENCE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( UNICODE_VALID_HIGH_NO_LOW_SURROGATE,
                                UNICODE_VALID_HIGH_NO_LOW_SURROGATE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( PREMATURE_UNICODE_LOW_SURROGATE,
                                PREMATURE_UNICODE_LOW_SURROGATE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( ILLEGAL_UNICODE_HIGH_SURROGATES,
                                ILLEGAL_UNICODE_HIGH_SURROGATES_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( UNICODE_ESCAPE_SEQUENCE_ZERO_CP,
                                UNICODE_ESCAPE_SEQUENCE_ZERO_CP_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( UNICODE_VALID_HIGH_INVALID_LOW_SURROGATE,
                                UNICODE_VALID_HIGH_INVALID_LOW_SURROGATE_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );
}

/**
 * @brief Test that JSON_Search can find the right value given a query key.
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

/**
 * @brief Test that a nested collection can only only have JSON_MAX_DEPTH levels
 * of nesting.
 */
void test_JSON_Max_Depth( void )
{
    JSONStatus_t jsonStatus;
    char * maxNestedObject, * maxNestedArray;

    maxNestedArray = allocateMaxDepthArray();
    jsonStatus = JSON_Validate( maxNestedArray,
                                strlen( maxNestedArray ) );
    TEST_ASSERT_EQUAL( JSONMaxDepthExceeded, jsonStatus );

    maxNestedObject = allocateMaxDepthObject();
    jsonStatus = JSON_Validate( maxNestedObject,
                                strlen( maxNestedObject ) );
    TEST_ASSERT_EQUAL( JSONMaxDepthExceeded, jsonStatus );

    free( maxNestedArray );
    free( maxNestedObject );
}

/**
 * @brief Test that JSON_Search can find the right value given an incorrect query
 * key or invalid JSON string.
 */
void test_JSON_Search_Invalid_JSON( void )
{
    JSONStatus_t jsonStatus;
    char * outValue;
    size_t outValueLength;

    jsonStatus = JSON_Search( SAMPLE_JSON_KEY_CUT,
                              SAMPLE_JSON_KEY_CUT_LEN,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Search( WHITE_SPACE,
                              WHITE_SPACE_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Search( CLOSING_CURLY_BRACKET,
                              CLOSING_CURLY_BRACKET_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONNotFound, jsonStatus );

    jsonStatus = JSON_Search( OPENING_CURLY_BRACKET,
                              OPENING_CURLY_BRACKET_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Search( INCORRECT_OBJECT_SEPARATOR,
                              INCORRECT_OBJECT_SEPARATOR_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Search( ILLEGAL_KEY_NOT_STRING,
                              ILLEGAL_KEY_NOT_STRING_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Search( WRONG_KEY_VALUE_SEPARATOR,
                              WRONG_KEY_VALUE_SEPARATOR_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Search( CUT_AFTER_KEY,
                              CUT_AFTER_KEY_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );
}
