#include <string.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "json.h"

/* Sample test from the docs. */
#define JSON_2_LEVELS                   "{\"foo\":\"abc\",\"bar\":{\"foo\",\"xyz\"}}"

#define JSON_2_LEVELS_TRAILING_COMMA    "{\"foo\":\"abc\",\"bar\":{\"foo\",\"xyz\",}}"

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
 * @brief Test that JSON_Validate is able to update the context object correctly.
 */
void test_JSON_Validate_Happy_Path( void )
{
    JSONStatus_t jsonStatus;

    jsonStatus = JSON_Validate( JSON_2_LEVELS, sizeof( JSON_2_LEVELS ) );
    TEST_ASSERT_EQUAL( JSONSuccess, jsonStatus );

    jsonStatus = JSON_Validate( JSON_2_LEVELS_TRAILING_COMMA, sizeof( JSON_2_LEVELS_TRAILING_COMMA ) );
    TEST_ASSERT_EQUAL( JSONIllegalDocument, jsonStatus );
}
