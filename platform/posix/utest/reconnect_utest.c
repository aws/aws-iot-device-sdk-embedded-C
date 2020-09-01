#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <errno.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "transport_reconnect.h"

#include "mock_time_api.h"
#include "mock_math_api.h"

/* Jitter upon resetting reconnect parameters. */
#define JITTER    ( MAX_JITTER_VALUE_SECONDS / ( MAX_RECONNECT_ATTEMPTS ) )

static TransportReconnectParams_t reconnectParams;

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
 * @brief A helper method to make assertions on the #TransportReconnectParams_t
 * object upon calling #Transport_ReconnectParamsReset.
 */
static void verifyReconnectParamsAfterReset( void )
{
    TEST_ASSERT_EQUAL( 0, reconnectParams.attemptsDone );
    TEST_ASSERT_EQUAL( JITTER, reconnectParams.nextJitterMax - JITTER );
    TEST_ASSERT_GREATER_OR_EQUAL_UINT32( INITIAL_RECONNECT_BACKOFF_SECONDS,
                                         reconnectParams.nextJitterMax );
    TEST_ASSERT_LESS_THAN_UINT32( ( INITIAL_RECONNECT_BACKOFF_SECONDS +
                                    MAX_JITTER_VALUE_SECONDS ),
                                  reconnectParams.nextJitterMax );
    TEST_ASSERT_LESS_THAN_UINT32( MAX_RECONNECT_ATTEMPTS,
                                  reconnectParams.attemptsDone );
}

/**
 * @brief Test that #Transport_ReconnectParamsReset initializes the #nextJitterMax
 * to be equal to the some configurable backoff plus jitter.
 */
void test_Transport_ReconnectParamsReset_Sets_Jitter_Correctly( void )
{
    rand_ExpectAndReturn( JITTER );
    Transport_ReconnectParamsReset( &reconnectParams );
    verifyReconnectParamsAfterReset();
}

/**
 * @brief Test that #Transport_ReconnectBackoffAndSleep is able to double the
 * max value of the next jitter and return false when all attempts are exhausted.
 *
 * @note #Transport_ReconnectParamsReset is expected to be called before
 * #Transport_ReconnectBackoffAndSleep.
 */
void test_Transport_ReconnectBackoffAndSleep_Succeeds( void )
{
    bool retriesArePending;
    int32_t expectedNextJitterMax = INITIAL_RECONNECT_BACKOFF_SECONDS;

    rand_ExpectAndReturn( JITTER );
    Transport_ReconnectParamsReset( &reconnectParams );
    verifyReconnectParamsAfterReset();

    expectedNextJitterMax = reconnectParams.nextJitterMax;

    while( reconnectParams.attemptsDone < MAX_RECONNECT_ATTEMPTS )
    {
        if( reconnectParams.nextJitterMax < ( MAX_RECONNECT_BACKOFF_SECONDS / 2U ) )
        {
            expectedNextJitterMax += expectedNextJitterMax;
        }
        else
        {
            expectedNextJitterMax = MAX_RECONNECT_BACKOFF_SECONDS;
        }

        /* Mock sleep, so the test can run faster. */
        rand_ExpectAndReturn( 0 );
        sleep_ExpectAnyArgsAndReturn( 0 );
        retriesArePending = Transport_ReconnectBackoffAndSleep( &reconnectParams );
        TEST_ASSERT_TRUE( retriesArePending );
        TEST_ASSERT_EQUAL( expectedNextJitterMax, reconnectParams.nextJitterMax );
        TEST_ASSERT_LESS_OR_EQUAL_UINT32( MAX_RECONNECT_ATTEMPTS,
                                          reconnectParams.attemptsDone );
    }

    /* The next call to the function under test should now return that all
     * attempts are now exhausted. */
    rand_ExpectAndReturn( JITTER );
    retriesArePending = Transport_ReconnectBackoffAndSleep( &reconnectParams );
    TEST_ASSERT_FALSE( retriesArePending );

    /* #Transport_ReconnectParamsReset is expected to be called once all attempts
     * are exhausted. */
    verifyReconnectParamsAfterReset();
}

/**
 * @brief Test that the value of the next max jitter has a lower bound that will
 * then be capped at some max threshold.
 */
void test_Transport_ReconnectBackoffAndSleep_Lower_Bound_Jitter_To_Cap( void )
{
    bool retriesArePending;

    /* Initialize to 0 attempts, so the max value of next jitter will increase. */
    reconnectParams.attemptsDone = 0U;
    reconnectParams.nextJitterMax = MAX_RECONNECT_BACKOFF_SECONDS / 2U;

    /* The next max jitter doubles on every retry unless it is greater than or
     * equal to half of the max threshold. */
    rand_ExpectAndReturn( 0 );
    sleep_ExpectAnyArgsAndReturn( 0 );
    retriesArePending = Transport_ReconnectBackoffAndSleep( &reconnectParams );
    TEST_ASSERT_TRUE( retriesArePending );
    TEST_ASSERT_EQUAL( reconnectParams.nextJitterMax,
                       MAX_RECONNECT_BACKOFF_SECONDS );
    TEST_ASSERT_LESS_THAN_UINT32( MAX_RECONNECT_ATTEMPTS,
                                  reconnectParams.attemptsDone );
}

/**
 * @brief Test that the value of the next max jitter has an upper bound that will
 * then be capped at some max threshold.
 */
void test_Transport_ReconnectBackoffAndSleep_Upper_Bound_Jitter_To_Cap( void )
{
    bool retriesArePending;

    /* Initialize to 0 attempts, so the max value of next jitter will increase. */
    reconnectParams.attemptsDone = 0U;
    reconnectParams.nextJitterMax = MAX_RECONNECT_BACKOFF_SECONDS - 1U;

    /* The next max jitter doubles on every retry unless it is greater than or
     * equal to half of the max threshold. */
    rand_ExpectAndReturn( 0 );
    sleep_ExpectAnyArgsAndReturn( 0 );
    retriesArePending = Transport_ReconnectBackoffAndSleep( &reconnectParams );
    TEST_ASSERT_TRUE( retriesArePending );
    TEST_ASSERT_EQUAL( reconnectParams.nextJitterMax,
                       MAX_RECONNECT_BACKOFF_SECONDS );
    TEST_ASSERT_LESS_THAN_UINT32( MAX_RECONNECT_ATTEMPTS,
                                  reconnectParams.attemptsDone );
}
