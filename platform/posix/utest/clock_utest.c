/*
 * AWS IoT Device SDK for Embedded C 202108.00
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

#include <stdbool.h>
#include <stdlib.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "clock.h"

#include "mock_time_api.h"

/* The amount of time to sleep, which is a parameter passed to #Clock_SleepMs. */
#define SLEEP_TIME_MS                  ( 500 )

/* Parameters to set for the #timespec in #Clock_GetTimeMs. */
#define GET_TIME_S                     ( 50 )
#define GET_TIME_NS                    ( 2500 )

/* Time conversion constants. */
#define NANOSECONDS_PER_MILLISECOND    ( 1000000L )    /**< @brief Nanoseconds per millisecond. */
#define MILLISECONDS_PER_SECOND        ( 1000L )

/**
 * @brief Used to make assertions on the arguments passed to #nanosleep
 * from #Clock_SleepMs.
 *
 * @param[in] requested_time The requested time to sleep.
 * @param[in] remaining The remaining time left to sleep.
 *
 * @return Successful status returned by #nanosleep or 0
 */
int nanosleep_validate_args( const struct timespec * requested_time,
                             struct timespec * remaining,
                             int numCalls )
{
    /* Suppress unused parameter warning. */
    ( void ) numCalls;

    TEST_ASSERT_NOT_NULL( requested_time );
    TEST_ASSERT_NULL( remaining );
    TEST_ASSERT_EQUAL( ( time_t ) SLEEP_TIME_MS / ( time_t ) MILLISECONDS_PER_SECOND,
                       requested_time->tv_sec );
    TEST_ASSERT_EQUAL( ( ( int64_t ) SLEEP_TIME_MS % MILLISECONDS_PER_SECOND )
                       * NANOSECONDS_PER_MILLISECOND,
                       requested_time->tv_nsec );

    return 0;
}

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
 * @brief Test that #Clock_GetTimeMs returns the expected time when there is no
 * possible overflow.
 */
void test_Clock_GetTimeMs_Returns_Expected_Time_No_Overflow( void )
{
    uint32_t actualTimeMs, expectedTimeMs;
    struct timespec timeSpec;

    /* This case will NOT cause the time to overflow. */
    timeSpec.tv_sec = GET_TIME_S;
    timeSpec.tv_nsec = GET_TIME_NS;

    clock_gettime_ExpectAnyArgsAndReturn( 0 );
    clock_gettime_ReturnThruPtr_time_point( &timeSpec );
    actualTimeMs = Clock_GetTimeMs();

    expectedTimeMs = ( timeSpec.tv_sec * MILLISECONDS_PER_SECOND )
                     + ( timeSpec.tv_nsec / NANOSECONDS_PER_MILLISECOND );

    TEST_ASSERT_EQUAL( expectedTimeMs, actualTimeMs );
}

/**
 * @brief Test that #Clock_GetTimeMs returns the expected time when there is a
 * guaranteed overflow.
 *
 * @note Overflow is allowed to happen as it is handled by the libraries. The
 * returned value is just the overflowed sum.
 */
void test_Clock_GetTimeMs_Returns_Expected_Time_Guaranteed_Overflow( void )
{
    uint32_t actualTimeMs, expectedTimeMs;
    struct timespec timeSpec;

    /* This case will cause the time to overflow. */
    timeSpec.tv_sec = LONG_MAX;
    timeSpec.tv_nsec = LONG_MAX;

    clock_gettime_ExpectAnyArgsAndReturn( 0 );
    clock_gettime_ReturnThruPtr_time_point( &timeSpec );
    actualTimeMs = Clock_GetTimeMs();

    expectedTimeMs = ( timeSpec.tv_sec * MILLISECONDS_PER_SECOND )
                     + ( timeSpec.tv_nsec / NANOSECONDS_PER_MILLISECOND );

    TEST_ASSERT_EQUAL( expectedTimeMs, actualTimeMs );
}

/**
 * @brief Test that the call to #nanosleep in #Clock_SleepMs receives the
 * expected parameter values.
 */
void test_Clock_SleepMs_Passes_Expected_Values_To_nanosleep()
{
    uint32_t sleepTimeMs = SLEEP_TIME_MS;

    nanosleep_Stub( nanosleep_validate_args );
    Clock_SleepMs( sleepTimeMs );
}
