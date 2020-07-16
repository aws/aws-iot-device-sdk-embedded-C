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

/**
 * @file clock_posix.c
 * @brief Implementation of the functions in clock.h for POSIX systems.
 */

/* POSIX include. Allow the default POSIX header to be overridden. */
#ifdef POSIX_TIME_HEADER
    #include POSIX_TIME_HEADER
#else
    #include <time.h>
#endif

/* Platform clock include. */
#include "clock.h"

/*
 * Time conversion constants.
 */
#define NANOSECONDS_PER_SECOND         ( 1000000000 ) /**< @brief Nanoseconds per second. */
#define NANOSECONDS_PER_MILLISECOND    ( 1000000 )    /**< @brief Nanoseconds per millisecond. */
#define MILLISECONDS_PER_SECOND        ( 1000 )       /**< @brief Milliseconds per second. */

/*-----------------------------------------------------------*/

uint32_t Clock_GetTimeMs( void )
{
    uint32_t timeMs;
    struct timespec timeSpec;

    /* Get the MONOTONIC time. */
    clock_gettime( CLOCK_MONOTONIC, &timeSpec );

    /* Calculate the milliseconds from timespec. */
    timeMs = ( uint32_t ) ( timeSpec.tv_sec * 1000 )
             + ( uint32_t ) ( timeSpec.tv_nsec / ( 1000 * 1000 ) );

    return timeMs;
}

/*-----------------------------------------------------------*/

void Clock_SleepMs( uint32_t sleepTimeMs )
{
    /* Convert parameter to timespec. */
    struct timespec sleepTime =
    {
        .tv_sec = sleepTimeMs / MILLISECONDS_PER_SECOND,
        .tv_nsec = ( sleepTimeMs % MILLISECONDS_PER_SECOND ) * NANOSECONDS_PER_MILLISECOND
    };

    /* High resolution sleep. */
    ( void ) nanosleep( &sleepTime, NULL );

    return;
}
