#include <string.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "json.h"

/* Sample test from the docs. */
#define JSON_QUERY_SEPARATOR                    '.'

#define SAMPLE_JSON                                                                  \
    "{\"literal\":true, \"more_literals\": {\"literal2\":false, \"literal3\":null}," \
    "\"exp1\": 5E+3, \"more_exponents\": [5e+2, 4e-2, 93E-5, 128E-6],  "             \
    "\"number\": -123412, "                                                          \
    "\"decimal\":109238.42091289, "                                                  \
    "\"foo\":\"abc\",\"bar\":{\"foo\":\"xyz\"}}"
#define SAMPLE_JSON_LEN                         ( sizeof( SAMPLE_JSON ) - 1 )

#define SAMPLE_JSON_QUERY_KEY                   "bar.foo"
#define SAMPLE_JSON_QUERY_KEY_LEN               ( sizeof( SAMPLE_JSON_QUERY_KEY ) - 1 )

#define JSON_EXPECTED_QUERY_ANSWER              "xyz"
#define JSON_EXPECTED_QUERY_ANSWER_LEN          ( sizeof( JSON_EXPECTED_QUERY_ANSWER ) - 1 )

#define SINGLE_SCALAR                           "\"4102985123a\""
#define SINGLE_SCALAR_LEN                       ( sizeof( SINGLE_SCALAR ) - 1 )

#define TRAILING_COMMA_AFTER_VALUE              "{\"foo\":\"abc\",\"bar\":{\"foo\" : \"xyz\",}}"
#define TRAILING_COMMA_AFTER_VALUE_LENGTH       ( sizeof( TRAILING_COMMA_AFTER_VALUE ) - 1 )

#define INCORRECT_OBJECT_SEPARATOR              "{\"foo\": \"bar\"; \"bar\": \"foo\"}"
#define INCORRECT_OBJECT_SEPARATOR_LENGTH       ( sizeof( INCORRECT_OBJECT_SEPARATOR ) - 1 )

#define SAMPLE_JSON_TRAILING_SPACES             "{\"foo\":\"abc\",\"bar\":{\"foo\" : \"xyz\"}}  "
#define SAMPLE_JSON_TRAILING_SPACES_LEN         ( sizeof( SAMPLE_JSON_TRAILING_SPACES ) - 1 )

#define SAMPLE_JSON_KEY_CUT                     "{\"foo\":\"abc\",\"bar\":{\""
#define SAMPLE_JSON_KEY_CUT_LEN                 ( sizeof( SAMPLE_JSON_KEY_CUT ) - 1 )

#define MULTIPLE_VALID_ESCAPES                  "\"\\\\ \\\" \\/ \\b \\f \\n \\r \\t \\\x12\" "
#define MULTIPLE_VALID_ESCAPES_LENGTH           ( sizeof( MULTIPLE_VALID_ESCAPES ) - 1 )

#define ILLEGAL_LEADING_ZEROS                   "07"
#define ILLEGAL_LEADING_ZEROS_LENGTH            ( sizeof( ILLEGAL_LEADING_ZEROS ) - 1 )

#define TRAILING_COMMA_IN_OBJECT                "[{\"hello\": [\"foo\",]}]"
#define TRAILING_COMMA_IN_OBJECT_LENGTH         ( sizeof( TRAILING_COMMA_IN_OBJECT ) - 1 )

#define NOTHING_AFTER_COMMA_SEPARATOR           "{\"hello\": [5,"
#define NOTHING_AFTER_COMMA_SEPARATOR_LENGTH    ( sizeof( NOTHING_AFTER_COMMA_SEPARATOR ) - 1 )

#define CLOSING_SQUARE_BRACKET                  "]"
#define CLOSING_SQUARE_BRACKET_LENGTH           ( sizeof( CLOSING_SQUARE_BRACKET ) - 1 )

#define CLOSING_CURLY_BRACKET                   "}"
#define CLOSING_CURLY_BRACKET_LENGTH            ( sizeof( CLOSING_CURLY_BRACKET ) - 1 )

#define OPENING_CURLY_BRACKET                   "{"
#define OPENING_CURLY_BRACKET_LENGTH            ( sizeof( OPENING_CURLY_BRACKET ) - 1 )

/*#define UNICODE_CHARS                      "\"\\u\xf0\x9f\xa7\x99\"" */
/*#define UNICODE_CHARS_LENGTH               ( sizeof( UNICODE_CHARS ) - 1 ) */

#define VALID_UTF8                                   "\"\xc2\xa9 \xe2\x98\x95 \xf0\x9f\x98\x80\""
#define VALID_UTF8_LENGTH                            ( sizeof( VALID_UTF8 ) - 1 )

#define INVALID_UTF8_PREMATURE_CUT                   "{\"foo\":\"abc\",\"bar\":{\"\xc2\xa9 "
#define INVALID_UTF8_PREMATURE_CUT_LENGTH            ( sizeof( INVALID_UTF8_PREMATURE_CUT ) - 1 )

#define WRONG_KEY_VALUE_SEPARATOR                    "{\"hello\";\"world\"}"
#define WRONG_KEY_VALUE_SEPARATOR_LENGTH             ( sizeof( WRONG_KEY_VALUE_SEPARATOR ) - 1 )

#define INVALID_UTF8_NEXT_BYTE                       "\"\xc2\x00\""
#define INVALID_UTF8_NEXT_BYTE_LENGTH                ( sizeof( INVALID_UTF8_NEXT_BYTE ) - 1 )

#define INVALID_UTF8_START_C1                        "\"\xc1\""
#define INVALID_UTF8_START_C1_LENGTH                 ( sizeof( INVALID_UTF8_START_C1 ) - 1 )

#define INVALID_UTF8_START_F5                        "\"\xf5\""
#define INVALID_UTF8_START_F5_LENGTH                 ( sizeof( INVALID_UTF8_START_F5 ) - 1 )

#define INVALID_UTF8_CUT                             "\"\xc2"
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

/* The following escapes are considered invalid. */
#define NUL_ESCAPE                                   "\"\\\x0\""
#define NUL_ESCAPE_LENGTH                            ( sizeof( NUL_ESCAPE ) - 1 )

#define ESCAPE_CHAR_ALONE                            "\"\\\""
#define ESCAPE_CHAR_ALONE_LENGTH                     ( sizeof( ESCAPE_CHAR_ALONE ) - 1 )

/* Triggers the case in which i < max for skipDigits. */
#define NOTHING_AFTER_NUMBER                         "{\"decimal\": 1"
#define NOTHING_AFTER_NUMBER_LENGTH                  ( sizeof( NOTHING_AFTER_NUMBER ) - 1 )

/* Triggers the case in which i < max for skipDecimals. */
#define NOTHING_AFTER_DECIMAL_POINT                  "{\"decimal\": 1."
#define NOTHING_AFTER_DECIMAL_POINT_LENGTH           ( sizeof( NOTHING_AFTER_DECIMAL_POINT ) - 1 )

/* Triggers the case in which i < max for skipEscape. */
#define ESCAPE_CHAR_ALONE_NOT_ENCLOSED               "\"\\"
#define ESCAPE_CHAR_ALONE_NOT_ENCLOSED_LENGTH        ( sizeof( ESCAPE_CHAR_ALONE_NOT_ENCLOSED ) - 1 )

/* Triggers the case in which i < max for skipExponent. */
#define NOTHING_AFTER_EXPONENT_MARKER                "4e"
#define NOTHING_AFTER_EXPONENT_MARKER_LENGTH         ( sizeof( NOTHING_AFTER_EXPONENT_MARKER ) - 1 )

/* Triggers the case in which i < max for skipString. */
#define WHITE_SPACE                                  "   "
#define WHITE_SPACE_LENGTH                           ( sizeof( WHITE_SPACE ) - 1 )

/* Triggers the case in which i < max for skipArrayScalars. */
#define NOTHING_AFTER_ARRAY_START_MARKER             "{\"hello\": ["
#define NOTHING_AFTER_ARRAY_START_MARKER_LENGTH      ( sizeof( NOTHING_AFTER_ARRAY_START_MARKER ) - 1 )

/* Triggers the cases in which i < max for skipObjectScalars. */
#define NOTHING_AFTER_OBJECT_START_MARKER            "{\"hello\": {"
#define NOTHING_AFTER_OBJECT_START_MARKER_LENGTH     ( sizeof( NOTHING_AFTER_OBJECT_START_MARKER ) - 1 )

#define NOTHING_AFTER_KEY                            "{\"hello\""
#define NOTHING_AFTER_KEY_LENGTH                     ( sizeof( NOTHING_AFTER_KEY ) - 1 )

/* A non-number after the exponent marker is illegal. */
#define INVALID_EXPONENT                             "5Ea"
#define INVALID_EXPONENT_LENGTH                      ( sizeof( INVALID_EXPONENT ) - 1 )

/* Illegal scalar entry in the array. */
#define ILLEGAL_SCALAR_IN_ARRAY                      "{\"hello\": [42, world]\""
#define ILLEGAL_SCALAR_IN_ARRAY_LENGTH               ( sizeof( ILLEGAL_SCALAR_IN_ARRAY ) - 1 )

/* Key is not a string. */
#define ILLEGAL_KEY_NOT_STRING                       "{key: true}"
#define ILLEGAL_KEY_NOT_STRING_LENGTH                ( sizeof( ILLEGAL_KEY_NOT_STRING ) - 1 )

#define UNKNOWN_ESCAPE                               "\"\\\x20\""
#define UNKNOWN_ESCAPE_LENGTH                        ( sizeof( UNKNOWN_ESCAPE ) - 1 )

/* An unescaped control character is considered invalid. */
#define UNESCAPED_CONTROL_CHAR                       "\"\x15\""
#define UNESCAPED_CONTROL_CHAR_LENGTH                ( sizeof( UNESCAPED_CONTROL_CHAR ) - 1 )


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

    jsonStatus = JSON_Validate( SAMPLE_JSON_TRAILING_SPACES,
                                SAMPLE_JSON_TRAILING_SPACES_LEN );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( MULTIPLE_VALID_ESCAPES, MULTIPLE_VALID_ESCAPES_LENGTH );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( VALID_UTF8, VALID_UTF8_LENGTH );
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

    jsonStatus = JSON_Validate( NOTHING_AFTER_COMMA_SEPARATOR,
                                NOTHING_AFTER_COMMA_SEPARATOR_LENGTH );
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

    jsonStatus = JSON_Validate( NOTHING_AFTER_NUMBER,
                                NOTHING_AFTER_NUMBER_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( NOTHING_AFTER_ARRAY_START_MARKER,
                                NOTHING_AFTER_ARRAY_START_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( NOTHING_AFTER_OBJECT_START_MARKER,
                                NOTHING_AFTER_OBJECT_START_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( NOTHING_AFTER_KEY,
                                NOTHING_AFTER_KEY_LENGTH );
    TEST_ASSERT_EQUAL( JSONPartial, jsonStatus );

    jsonStatus = JSON_Validate( WRONG_KEY_VALUE_SEPARATOR,
                                WRONG_KEY_VALUE_SEPARATOR_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( NOTHING_AFTER_EXPONENT_MARKER,
                                NOTHING_AFTER_EXPONENT_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( MISSING_ENCLOSING_ARRAY_MARKER,
                                MISSING_ENCLOSING_ARRAY_MARKER_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( INVALID_EXPONENT,
                                INVALID_EXPONENT_LENGTH );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );

    jsonStatus = JSON_Validate( NOTHING_AFTER_DECIMAL_POINT,
                                NOTHING_AFTER_DECIMAL_POINT_LENGTH );
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
 * @brief Test that JSON_Search can find the right value given an incorrect query key
 * or invalid JSON string.
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

    jsonStatus = JSON_Search( NOTHING_AFTER_KEY,
                              NOTHING_AFTER_KEY_LENGTH,
                              SAMPLE_JSON_QUERY_KEY,
                              SAMPLE_JSON_QUERY_KEY_LEN,
                              JSON_QUERY_SEPARATOR,
                              &outValue,
                              &outValueLength );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );
}
