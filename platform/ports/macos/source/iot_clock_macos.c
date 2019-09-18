/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_clock_macos.c
 * @brief Implementation of the functions in iot_clock.h for macOS.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Platform clock include. */
#include "platform/iot_clock.h"

/* Standard includes. */
#include <stdlib.h>

/* POSIX includes. Allow the default POSIX headers to be overridden. */
#ifdef POSIX_ERRNO_HEADER
    #include POSIX_ERRNO_HEADER
#else
    #include <errno.h>
#endif
#ifdef POSIX_TIME_HEADER
    #include POSIX_TIME_HEADER
#else
    #include <time.h>
#endif

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_PLATFORM
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_PLATFORM
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "CLOCK" )
#include "iot_logging_setup.h"

/*-----------------------------------------------------------*/

/**
 * @brief The format of timestrings printed in logs.
 *
 * For more information on timestring formats, see [this link.]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/strftime.html)
 */
#define TIMESTRING_FORMAT              ( "%F %R:%S" )

/*
 * Time conversion constants.
 */
#define NANOSECONDS_PER_MILLISECOND    ( 1000000 ) /**< @brief Nanoseconds per millisecond. */
#define MILLISECONDS_PER_SECOND        ( 1000 )    /**< @brief Milliseconds per second. */

/*-----------------------------------------------------------*/

/**
 * @brief Wraps an #IotThreadRoutine_t with a GCD-compliant one.
 *
 * @param[in] pArgument The value passed to `dispatch_after_f`.
 */
static void _timerExpirationWrapper( void * pArgument );

/*-----------------------------------------------------------*/

static void _timerExpirationWrapper( void * pArgument )
{
    IotTimer_t * pTimer = pArgument;

    /* Invoke the wrapped expiration routine. */
    pTimer->threadRoutine( pTimer->pArgument );
}

/*-----------------------------------------------------------*/

bool IotClock_GetTimestring( char * pBuffer,
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

/*-----------------------------------------------------------*/

uint64_t IotClock_GetTimeMs( void )
{
    struct timespec currentTime = { 0 };

    if( clock_gettime( CLOCK_MONOTONIC, &currentTime ) != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to read time from CLOCK_MONOTONIC. errno=%d",
                     errno );

        abort();
    }

    return ( ( uint64_t ) currentTime.tv_sec ) * MILLISECONDS_PER_SECOND +
           ( ( uint64_t ) currentTime.tv_nsec ) / NANOSECONDS_PER_MILLISECOND;
}

/*-----------------------------------------------------------*/

void IotClock_SleepMs( uint32_t sleepTimeMs )
{
    /* Convert parameter to timespec. */
    struct timespec sleepTime =
    {
        .tv_sec  = sleepTimeMs / MILLISECONDS_PER_SECOND,
        .tv_nsec = ( sleepTimeMs % MILLISECONDS_PER_SECOND ) * NANOSECONDS_PER_MILLISECOND
    };

    if( nanosleep( &sleepTime, NULL ) == -1 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Sleep failed. errno=%d.", errno );

        abort();
    }
}

/*-----------------------------------------------------------*/

bool IotClock_TimerCreate( IotTimer_t * pNewTimer,
                           IotThreadRoutine_t expirationRoutine,
                           void * pArgument )
{
    pNewTimer->dispatchBlock = NULL;

    /* Save the expiration routine and argument for use later. */
    pNewTimer->pArgument = pArgument;
    pNewTimer->threadRoutine = expirationRoutine;

    return true;
}

/*-----------------------------------------------------------*/

void IotClock_TimerDestroy( IotTimer_t * pTimer )
{
    /* Cancel any timer work that may already be scheduled. */
    if( pTimer->dispatchBlock != NULL )
    {
        dispatch_block_cancel( pTimer->dispatchBlock );

        /* dispatch_release only needs to be called if ARC is not being used. */
        #if( OS_OBJECT_HAVE_OBJC_SUPPORT == 0 )
            dispatch_release( pTimer->dispatchBlock );
        #endif
    }
}

/*-----------------------------------------------------------*/

bool IotClock_TimerArm( IotTimer_t * pTimer,
                        uint32_t relativeTimeoutMs,
                        uint32_t periodMs )
{
    bool status = true;

    /* Get the handle to a global concurrent queue. Work will be submitted to
     * this queue. */
    dispatch_queue_t globalDispatchQueue = dispatch_get_global_queue( QOS_CLASS_DEFAULT, 0 );

    /* Calculate when the timer should first expire. */
    int64_t delta = ( int64_t ) relativeTimeoutMs * NANOSECONDS_PER_MILLISECOND;
    dispatch_time_t timeout = dispatch_time( DISPATCH_TIME_NOW, delta );

    /* Save the period. */
    pTimer->periodMs = periodMs;

    /* Cancel any timer work that may already be scheduled (in case this call
     * is a reschedule of an existing timer). */
    IotClock_TimerDestroy( pTimer );

    /* Create a dispatch block to execute work on behalf of the timer. */
    pTimer->dispatchBlock = dispatch_block_create( 0, ^ {
        _timerExpirationWrapper( pTimer );
    } );

    if( pTimer->dispatchBlock == NULL )
    {
        IotLogError( "Failed to create timer dispatch block." );

        status = false;
    }
    else
    {
        /* Schedule the timer expiration to run at the timeout. */
        dispatch_after( timeout, globalDispatchQueue, pTimer->dispatchBlock );
    }

    return status;
}

/*-----------------------------------------------------------*/
