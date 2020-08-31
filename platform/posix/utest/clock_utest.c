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
 */

#include <stdbool.h>
#include <stdlib.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "clock.h"

/* The number of iterations to run when testing #Clock_GetTimeMs. */
#define GET_TIME_ITERATIONS      ( 5 )
/* The number of iterations to run when testing #Clock_SleepMs. */
#define SLEEP_TIME_ITERATIONS    ( 5 )
/* The amount of time to sleep, which is a parameter passed to #Clock_SleepMs. */
#define SLEEP_TIME_MS            ( 1 )
/* The amount of excess time to tolerate when checking how much time has elapsed. */
#define SLEEP_TOLERANCE_MS       ( 3 )

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
 * @brief Test that #Clock_GetTimeMs is monotonically increasing.
 */
void test_Clock_GetTimeMs_Is_Monotonic( void )
{
    uint32_t prevTime = 0, curTime = 1;
    uint16_t t;

    for( t = 0; t < GET_TIME_ITERATIONS; t++ )
    {
        Clock_SleepMs( SLEEP_TIME_MS );
        curTime = Clock_GetTimeMs();

        /* Equality is not asserted because instructions may take longer
         * to execute depending on the CPU running the test. */
        TEST_ASSERT_GREATER_THAN_UINT32( prevTime, curTime );

        /* Test that the elapsed time is not larger than the time we slept plus
         * some tolerance for slower CPUs. */
        if( prevTime != 0 )
        {
            TEST_ASSERT_LESS_OR_EQUAL_UINT32( prevTime + SLEEP_TIME_MS + SLEEP_TOLERANCE_MS,
                                              curTime );
        }

        prevTime = curTime;
    }
}

/**
 * @brief Test that #Clock_SleepMs sleeps within a specified tolerance.
 */
void test_Clock_SleepMs_Is_Sleep()
{
    uint32_t timeBeforeSleep, timeAfterSleep, timeSlept;
    uint16_t t;

    for( t = 0; t < SLEEP_TIME_ITERATIONS; t++ )
    {
        timeBeforeSleep = Clock_GetTimeMs();
        Clock_SleepMs( SLEEP_TIME_MS );
        timeAfterSleep = Clock_GetTimeMs();
        timeSlept = timeAfterSleep - timeBeforeSleep;

        /* Equality is not asserted because instructions may take longer
         * to execute depending on the CPU running the test. */
        TEST_ASSERT_GREATER_OR_EQUAL_UINT32( SLEEP_TIME_MS, timeSlept );

        /* Test that the the time slept is not longer than the elapsed time plus
         * some tolerance for slower CPUs. */
        TEST_ASSERT_LESS_OR_EQUAL_UINT32( SLEEP_TIME_MS + SLEEP_TOLERANCE_MS,
                                          timeSlept );
    }
}
