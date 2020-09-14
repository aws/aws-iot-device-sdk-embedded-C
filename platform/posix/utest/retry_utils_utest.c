/*
 * AWS IoT Device SDK for Embedded C V202009.00
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
 */

#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include "/usr/include/errno.h"

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "retry_utils.h"

#include "mock_time_api.h"
#include "mock_math_api.h"

/* Return value of mocked #rand. */
#define RAND_RET_VAL            ( MAX_JITTER_VALUE_SECONDS + ( MAX_JITTER_VALUE_SECONDS / ( MAX_RETRY_ATTEMPTS ) ) )
#define EXPECTED_NEXT_JITTER    ( RAND_RET_VAL % MAX_JITTER_VALUE_SECONDS )
/* Parameters to track the next max jitter or number of attempts done. */
static RetryUtilsParams_t retryParams;
/* Return value of #RetryUtils_BackoffAndSleep. */
static RetryUtilsStatus_t retryUtilsStatus;

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
}

/* Called after each test method. */
void tearDown()
{
    retryUtilsStatus = false;
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
 * @brief A helper method to make assertions on the #RetryUtilsParams_t
 * object upon calling #RetryUtils_ParamsReset.
 */
static void verifyRetryParamsAfterReset( void )
{
    TEST_ASSERT_EQUAL( 0, retryParams.attemptsDone );
    TEST_ASSERT_EQUAL( INITIAL_RETRY_BACKOFF_SECONDS + EXPECTED_NEXT_JITTER,
                       retryParams.nextJitterMax );
    TEST_ASSERT_GREATER_OR_EQUAL_UINT32( INITIAL_RETRY_BACKOFF_SECONDS,
                                         retryParams.nextJitterMax );
    TEST_ASSERT_LESS_THAN_UINT32( ( INITIAL_RETRY_BACKOFF_SECONDS +
                                    MAX_JITTER_VALUE_SECONDS ),
                                  retryParams.nextJitterMax );
}

/**
 * @brief Test that #RetryUtils_ParamsReset initializes the #nextJitterMax
 * to be equal to some configurable backoff plus jitter.
 */
void test_RetryUtils_ParamsReset_Sets_Jitter_Correctly( void )
{
    clock_gettime_ExpectAnyArgsAndReturn( 0 );
    rand_ExpectAndReturn( RAND_RET_VAL );
    RetryUtils_ParamsReset( &retryParams );
    verifyRetryParamsAfterReset();
}

/**
 * @brief Test that #RetryUtils_BackoffAndSleep is able to double the
 * max value of the next jitter and return false when all attempts are exhausted.
 *
 * @note #RetryUtils_ParamsReset is expected to be called before
 * #RetryUtils_BackoffAndSleep.
 */
void test_RetryUtils_BackoffAndSleep_Succeeds( void )
{
    uint32_t expectedNextJitterMax = INITIAL_RETRY_BACKOFF_SECONDS;
    uint32_t expectedAttemptsDone = 0;

    clock_gettime_ExpectAnyArgsAndReturn( 0 );
    rand_ExpectAndReturn( RAND_RET_VAL );
    RetryUtils_ParamsReset( &retryParams );
    verifyRetryParamsAfterReset();

    expectedNextJitterMax = retryParams.nextJitterMax;

    while( retryParams.attemptsDone < MAX_RETRY_ATTEMPTS )
    {
        /* Simulate another iteration of the function under test. */
        rand_ExpectAndReturn( RAND_RET_VAL );
        sleep_ExpectAndReturn( RAND_RET_VAL % retryParams.nextJitterMax, 0 );
        retryUtilsStatus = RetryUtils_BackoffAndSleep( &retryParams );

        /* Updated the expected values of the parameters we expect. */
        expectedAttemptsDone++;

        if( retryParams.nextJitterMax < ( MAX_RETRY_BACKOFF_SECONDS / 2U ) )
        {
            expectedNextJitterMax += expectedNextJitterMax;
        }
        else
        {
            expectedNextJitterMax = MAX_RETRY_BACKOFF_SECONDS;
        }

        /* Verify our assertions. */
        TEST_ASSERT_EQUAL( RetryUtilsSuccess, retryUtilsStatus );
        TEST_ASSERT_EQUAL( expectedNextJitterMax, retryParams.nextJitterMax );
        TEST_ASSERT_EQUAL( expectedAttemptsDone, retryParams.attemptsDone );
    }

    /* The next call to the function under test should now return that all
     * attempts are now exhausted. */
    clock_gettime_ExpectAnyArgsAndReturn( 0 );
    rand_ExpectAndReturn( RAND_RET_VAL );
    retryUtilsStatus = RetryUtils_BackoffAndSleep( &retryParams );
    TEST_ASSERT_EQUAL( RetryUtilsRetriesExhausted, retryUtilsStatus );

    /* #RetryUtils_ParamsReset is expected to be called once all attempts
     * are exhausted. */
    verifyRetryParamsAfterReset();
}

/**
 * @brief Test that the value of the next max jitter has a lower bound that will
 * then be capped at some max threshold.
 */
void test_RetryUtils_BackoffAndSleep_Lower_Bound_Jitter_To_Cap( void )
{
    /* Initialize to 0 attempts, so the max value of next jitter will increase. */
    retryParams.attemptsDone = 0U;
    retryParams.nextJitterMax = ( MAX_RETRY_BACKOFF_SECONDS / 2U ) + 1;

    /* The next max jitter doubles on every retry unless it is greater than or
     * equal to half of the max threshold. In this case, the next jitter is
     * set to the retry. */
    rand_ExpectAndReturn( RAND_RET_VAL );
    sleep_ExpectAndReturn( RAND_RET_VAL % retryParams.nextJitterMax, 0 );
    retryUtilsStatus = RetryUtils_BackoffAndSleep( &retryParams );
    TEST_ASSERT_EQUAL( RetryUtilsSuccess, retryUtilsStatus );
    TEST_ASSERT_EQUAL( retryParams.nextJitterMax,
                       MAX_RETRY_BACKOFF_SECONDS );
    TEST_ASSERT_EQUAL( 1U, retryParams.attemptsDone );
}

/**
 * @brief Test that the value of the next max jitter has an upper bound that will
 * then be capped at some max threshold.
 */
void test_RetryUtils_BackoffAndSleep_Upper_Bound_Jitter_To_Cap( void )
{
    /* Initialize to 0 attempts, so the max value of next jitter will increase. */
    retryParams.attemptsDone = 0U;
    retryParams.nextJitterMax = MAX_RETRY_BACKOFF_SECONDS - 1U;

    /* The next max jitter doubles on every retry unless it is greater than or
     * equal to half of the max threshold. In this case, the next jitter is
     * set to the largest value for which its next value will change but not
     * double after retrying. */
    rand_ExpectAndReturn( RAND_RET_VAL );
    sleep_ExpectAndReturn( RAND_RET_VAL % retryParams.nextJitterMax, 0 );
    retryUtilsStatus = RetryUtils_BackoffAndSleep( &retryParams );
    TEST_ASSERT_EQUAL( RetryUtilsSuccess, retryUtilsStatus );
    TEST_ASSERT_EQUAL( retryParams.nextJitterMax,
                       MAX_RETRY_BACKOFF_SECONDS );
    TEST_ASSERT_EQUAL( 1U, retryParams.attemptsDone );
}
