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
 * @file iot_clock_win32.c
 * @brief Implementation of the functions in iot_clock.h for Win32 systems.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* Platform clock include. */
#include "platform/iot_clock.h"

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

/* Logging macro for Win32 errors. */
#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
    #include <strsafe.h>

    #define _logWin32TimerError( pTimer, pMessage )                          \
    {                                                                        \
        char * pErrorMessage = NULL;                                         \
                                                                             \
        FormatMessageA( FORMAT_MESSAGE_ALLOCATE_BUFFER |                     \
                        FORMAT_MESSAGE_FROM_SYSTEM |                         \
                        FORMAT_MESSAGE_IGNORE_INSERTS,                       \
                        NULL,                                                \
                        GetLastError(),                                      \
                        0,                                                   \
                        ( LPSTR ) ( &pErrorMessage ),                        \
                        0,                                                   \
                        NULL );                                              \
        pErrorMessage[ strlen( pErrorMessage ) - 3 ] = '\0';                 \
                                                                             \
        IotLogError( "(Timer %p) %s %s.", pTimer, pMessage, pErrorMessage ); \
        LocalFree( pErrorMessage );                                          \
    }
#else /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */
    #define _logWin32TimerError( pTimer, pMessage )
#endif /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */

/*-----------------------------------------------------------*/

/**
 * @brief Wraps an #IotThreadRoutine_t with a Win32-compliant one.
 *
 * @param[in] pArgument The value passed as `Parameter` to `CreateTimerQueueTimer`.
 * @param[in] timerOrWaitFired Ignored.
 */
static VOID CALLBACK _timerExpirationWrapper( _In_ PVOID pArgument,
                                              _In_ BOOLEAN timerOrWaitFired );

/*-----------------------------------------------------------*/

static VOID CALLBACK _timerExpirationWrapper( _In_ PVOID pArgument,
                                              _In_ BOOLEAN timerOrWaitFired )
{
    IotTimer_t * pTimer = ( IotTimer_t * ) pArgument;

    /* Silence warnings about unused parameters. */
    UNREFERENCED_PARAMETER( timerOrWaitFired );

    /* Call the wrapped thread routine. */
    pTimer->threadRoutine( pTimer->pArgument );
}

/*-----------------------------------------------------------*/

bool IotClock_GetTimestring( char * pBuffer,
                             size_t bufferSize,
                             size_t * pTimestringLength )
{
    bool status = true;
    int timestringLength = 0;
    SYSTEMTIME systemTime = { 0 };

    /* Get the Win32 system time and format it in the given buffer. */
    GetSystemTime( &systemTime );

    timestringLength = snprintf( pBuffer,
                                 bufferSize,
                                 "%u-%02u-%02u %02u:%02u:%02u.%03u",
                                 systemTime.wYear,
                                 systemTime.wMonth,
                                 systemTime.wDay,
                                 systemTime.wHour,
                                 systemTime.wMinute,
                                 systemTime.wSecond,
                                 systemTime.wMilliseconds );

    /* Check for errors from snprintf. */
    if( timestringLength < 0 )
    {
        /* Encoding error. */
        status = false;
    }
    else if( ( size_t ) timestringLength >= bufferSize )
    {
        /* Buffer too small. */
        status = false;
    }
    else
    {
        /* Success; set the output parameter. */
        *pTimestringLength = ( size_t ) timestringLength;
    }

    return status;
}

/*-----------------------------------------------------------*/

uint64_t IotClock_GetTimeMs( void )
{
    return ( uint64_t ) GetTickCount64();
}

/*-----------------------------------------------------------*/

void IotClock_SleepMs( uint32_t sleepTimeMs )
{
    Sleep( ( DWORD ) sleepTimeMs );
}

/*-----------------------------------------------------------*/

bool IotClock_TimerCreate( IotTimer_t * pNewTimer,
                           IotThreadRoutine_t expirationRoutine,
                           void * pArgument )
{
    /* Set the members of the new timer. */
    pNewTimer->pArgument = pArgument;
    pNewTimer->threadRoutine = expirationRoutine;
    pNewTimer->timer = INVALID_HANDLE_VALUE;

    return true;
}

/*-----------------------------------------------------------*/

void IotClock_TimerDestroy( IotTimer_t * pTimer )
{
    BOOL timerStatus = 0;

    if( pTimer->timer != INVALID_HANDLE_VALUE )
    {
        timerStatus = DeleteTimerQueueTimer( NULL,
                                             pTimer->timer,
                                             NULL );

        if( timerStatus == 0 )
        {
            _logWin32TimerError( pTimer, "Failed to destroy timer." );
            abort();
        }

        IotLogDebug( "(Timer %p) Timer destroyed.", pTimer );
        pTimer->timer = INVALID_HANDLE_VALUE;
    }
}

/*-----------------------------------------------------------*/

bool IotClock_TimerArm( IotTimer_t * pTimer,
                        uint32_t relativeTimeoutMs,
                        uint32_t periodMs )
{
    BOOL timerStatus = 0;

    /* Any previous timer must be destroyed before scheduling a new one in the
     * Win32 API. */
    IotClock_TimerDestroy( pTimer );

    timerStatus = CreateTimerQueueTimer( &( pTimer->timer ),
                                         NULL,
                                         _timerExpirationWrapper,
                                         pTimer,
                                         ( DWORD ) relativeTimeoutMs,
                                         ( DWORD ) periodMs,
                                         WT_EXECUTEDEFAULT );

    if( timerStatus == 0 )
    {
        _logWin32TimerError( pTimer, "Failed to create timer." );
    }
    else
    {
        IotLogDebug( "(Timer %p) Timer armed with timeout %lu and period %lu.",
                     pTimer,
                     ( unsigned long ) relativeTimeoutMs,
                     ( unsigned long ) periodMs );
    }

    return( timerStatus != 0 );
}

/*-----------------------------------------------------------*/
