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
 * @file iot_clock_posix.c
 * @brief Implementation of the functions in iot_clock.h for POSIX systems.
 */

/* The config header is always included first. */
#include "config.h"

/* Standard includes. */
#include <stdlib.h>

/* POSIX include. Allow the default POSIX header to be overridden. */
#ifdef POSIX_TIME_HEADER
    #include POSIX_TIME_HEADER
#else
    #include <time.h>
#endif

/* Platform clock include. */
#include "clock.h"

/* Configure logs for the functions in this file. */
#ifdef LOG_LEVEL_PLATFORM
    #define LIBRARY_LOG_LEVEL        LOG_LEVEL_PLATFORM
#else
    #ifdef LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "CLOCK" )
#include "logging_setup.h"

/*-----------------------------------------------------------*/

/**
 * @brief The format of timestrings printed in logs.
 *
 * For more information on timestring formats, see [this link.]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/strftime.html)
 */
#define TIMESTRING_FORMAT    ( "%F %R:%S" )

/*-----------------------------------------------------------*/

bool Clock_GetTimestring( char * pBuffer,
                          size_t bufferSize,
                          size_t * pTimestringLength )
{
    bool status = true;
    const time_t unixTime = time( NULL );
    struct tm localTime = { 0 };
    size_t timestringLength = 0;

    /* localtime_r is the thread-safe variant of localtime. Its return value
     * should be the pointer to the localTime struct. */
    if( localtime_r( &unixTime, &localTime ) != &localTime )
    {
        status = false;
    }

    if( status == true )
    {
        /* Convert the localTime struct to a string. */
        timestringLength = strftime( pBuffer, bufferSize, TIMESTRING_FORMAT, &localTime );

        /* Check for error from strftime. */
        if( timestringLength == 0 )
        {
            status = false;
        }
        else
        {
            /* Set the output parameter. */
            *pTimestringLength = timestringLength;
        }
    }

    return status;
}
