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
 * @file iot_threads_win32.c
 * @brief Implementation of the functions in iot_threads.h for Win32 systems.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdlib.h>

/* Windows include. */
#include <windows.h>

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Atomic include. */
#include "iot_atomic.h"

/* Error handling include. */
#include "private/iot_error.h"

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

#define LIBRARY_LOG_NAME    ( "THREAD" )
#include "iot_logging_setup.h"

/* Logging macro for Win32 errors. */
#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
    #include <strsafe.h>

    #define _logWin32Error( pName, pObject, pMessage )                            \
    {                                                                             \
        char * pErrorMessage = NULL;                                              \
                                                                                  \
        FormatMessageA( FORMAT_MESSAGE_ALLOCATE_BUFFER |                          \
                        FORMAT_MESSAGE_FROM_SYSTEM |                              \
                        FORMAT_MESSAGE_IGNORE_INSERTS,                            \
                        NULL,                                                     \
                        GetLastError(),                                           \
                        0,                                                        \
                        ( LPSTR ) ( &pErrorMessage ),                             \
                        0,                                                        \
                        NULL );                                                   \
        pErrorMessage[ strlen( pErrorMessage ) - 3 ] = '\0';                      \
                                                                                  \
        IotLogError( "(%s %p) %s %s.", pName, pObject, pMessage, pErrorMessage ); \
        LocalFree( pErrorMessage );                                               \
    }
#else /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */
    #define _logWin32Error( pName, pObject, pMessage )
#endif /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */

/*
 * Provide default values for undefined memory allocation functions.
 */
#ifndef IotThreads_Malloc
    #include <stdlib.h>

/**
 * @brief Memory allocation. This function should have the same signature
 * as [malloc](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define IotThreads_Malloc    malloc
#endif
#ifndef IotThreads_Free
    #include <stdlib.h>

/**
 * @brief Free memory. This function should have the same signature as
 * [free](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define IotThreads_Free    free
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Holds information about an active detached thread.
 */
typedef struct _threadInfo
{
    void * pArgument;                 /**< @brief First argument to `threadRoutine`. */
    IotThreadRoutine_t threadRoutine; /**< @brief Thread function to run. */
} _threadInfo_t;

/*-----------------------------------------------------------*/

/**
 * @brief Wraps an #IotThreadRoutine_t with a Win32-compliant one.
 *
 * @param[in] pArgument The value passed as `lpParameter` to `CreateThread`.
 *
 * @return Does not return, calls `ExitThread` with an exit code of `0`.
 */
static DWORD WINAPI _threadRoutineWrapper( _In_ LPVOID pArgument );

/*-----------------------------------------------------------*/

static DWORD WINAPI _threadRoutineWrapper( _In_ LPVOID pArgument )
{
    /* Cast argument to correct type. */
    _threadInfo_t * pThreadInfo = ( _threadInfo_t * ) pArgument;

    /* Read thread routine and argument, then free thread info. */
    IotThreadRoutine_t threadRoutine = pThreadInfo->threadRoutine;
    void * pThreadRoutineArgument = pThreadInfo->pArgument;

    IotThreads_Free( pThreadInfo );

    /* Run the thread routine. */
    threadRoutine( pThreadRoutineArgument );

    ExitThread( 0 );
}

/*-----------------------------------------------------------*/

bool Iot_CreateDetachedThread( IotThreadRoutine_t threadRoutine,
                               void * pArgument,
                               int32_t priority,
                               size_t stackSize )
{
    IOT_FUNCTION_ENTRY( bool, true );
    HANDLE newThread = NULL;
    _threadInfo_t * pThreadInfo = NULL;

    /* Determine the stack size of the thread to create. */
    SIZE_T threadStackSize = 0;

    if( stackSize != IOT_THREAD_DEFAULT_STACK_SIZE )
    {
        threadStackSize = ( SIZE_T ) stackSize;
    }

    /* Allocate memory for a new thread info. */
    pThreadInfo = IotThreads_Malloc( sizeof( _threadInfo_t ) );

    if( pThreadInfo == NULL )
    {
        IotLogError( "Failed to allocate memory for new thread." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Set the members of the thread info and create a new thread. */
    pThreadInfo->pArgument = pArgument;
    pThreadInfo->threadRoutine = threadRoutine;

    newThread = CreateThread( NULL,
                              threadStackSize,
                              _threadRoutineWrapper,
                              pThreadInfo,
                              0,
                              NULL );

    if( newThread == NULL )
    {
        IotLogError( "Failed to create new thread." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }
    else
    {
        IotLogDebug( "(Thread %p) New thread created.", newThread );

        /* Close the thread handle; it's not needed. This won't terminate the thread. */
        if( CloseHandle( newThread ) == 0 )
        {
            _logWin32Error( "Thread", newThread, "Failed to close thread handle." );
            abort();
        }
    }

    /* Clean up on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status == false )
    {
        if( pThreadInfo != NULL )
        {
            IotThreads_Free( pThreadInfo );
        }
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

bool IotMutex_Create( IotMutex_t * pNewMutex,
                      bool recursive )
{
    /* The Win32 critical section is always recursive, so this parameter is
     * ignored. */
    UNREFERENCED_PARAMETER( recursive );

    InitializeCriticalSection( pNewMutex );

    return true;
}

/*-----------------------------------------------------------*/

void IotMutex_Destroy( IotMutex_t * pMutex )
{
    DeleteCriticalSection( pMutex );
}

/*-----------------------------------------------------------*/

void IotMutex_Lock( IotMutex_t * pMutex )
{
    EnterCriticalSection( pMutex );
}

/*-----------------------------------------------------------*/

bool IotMutex_TryLock( IotMutex_t * pMutex )
{
    bool status = true;

    if( TryEnterCriticalSection( pMutex ) == 0 )
    {
        IotLogDebug( "(Mutex %p) Mutex not available.", pMutex );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotMutex_Unlock( IotMutex_t * pMutex )
{
    LeaveCriticalSection( pMutex );
}

/*-----------------------------------------------------------*/

bool IotSemaphore_Create( IotSemaphore_t * pNewSemaphore,
                          uint32_t initialValue,
                          uint32_t maxValue )
{
    bool status = true;

    /* Create a Win32 semaphore exclusive to this process. */
    pNewSemaphore->semaphore = CreateSemaphoreA( NULL,
                                                 ( LONG ) initialValue,
                                                 ( LONG ) maxValue,
                                                 NULL );

    if( pNewSemaphore->semaphore == NULL )
    {
        _logWin32Error( "Semaphore", pNewSemaphore, "Failed to create new semaphore." );

        status = false;
    }
    else
    {
        /* Set initial semaphore count. */
        pNewSemaphore->count = initialValue;
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotSemaphore_Destroy( IotSemaphore_t * pSemaphore )
{
    if( CloseHandle( pSemaphore->semaphore ) == 0 )
    {
        /* This should never happen, log an error and abort if it does. */
        _logWin32Error( "Semaphore", pSemaphore, "Failed to close semaphore handle." );

        abort();
    }
}

/*-----------------------------------------------------------*/

uint32_t IotSemaphore_GetCount( IotSemaphore_t * pSemaphore )
{
    return Atomic_Add_u32( &( pSemaphore->count ), 0 );
}

/*-----------------------------------------------------------*/

void IotSemaphore_Wait( IotSemaphore_t * pSemaphore )
{
    if( WaitForSingleObject( pSemaphore->semaphore, INFINITE ) != WAIT_OBJECT_0 )
    {
        /* This should never happen, log an error and abort if it does. */
        _logWin32Error( "Semaphore", pSemaphore, "Failed to wait on semaphore." );

        abort();
    }

    if( Atomic_Decrement_u32( &( pSemaphore->count ) ) == 0 )
    {
        IotLogError( "(Semaphore %p) Semaphore count decremented beyond 0.", pSemaphore );

        abort();
    }
}

/*-----------------------------------------------------------*/

bool IotSemaphore_TryWait( IotSemaphore_t * pSemaphore )
{
    return IotSemaphore_TimedWait( pSemaphore, 0 );
}

/*-----------------------------------------------------------*/

bool IotSemaphore_TimedWait( IotSemaphore_t * pSemaphore,
                             uint32_t timeoutMs )
{
    DWORD status = 0;

    status = WaitForSingleObject( pSemaphore->semaphore, ( DWORD ) timeoutMs );

    if( status == WAIT_OBJECT_0 )
    {
        if( Atomic_Decrement_u32( &( pSemaphore->count ) ) == 0 )
        {
            IotLogError( "(Semaphore %p) Semaphore count decremented beyond 0.", pSemaphore );

            abort();
        }
    }
    else if( status != WAIT_TIMEOUT )
    {
        /* This should never happen, log an error and abort if it does. */
        _logWin32Error( "Semaphore", pSemaphore, "Failed to wait on semaphore." );

        abort();
    }

    return( status == WAIT_OBJECT_0 );
}

/*-----------------------------------------------------------*/

void IotSemaphore_Post( IotSemaphore_t * pSemaphore )
{
    Atomic_Increment_u32( &( pSemaphore->count ) );

    if( ReleaseSemaphore( pSemaphore->semaphore, 1, NULL ) == 0 )
    {
        /* This should never happen, log an error and abort if it does. */
        _logWin32Error( "Semaphore", pSemaphore, "Failed to post to semaphore." );

        abort();
    }
}

/*-----------------------------------------------------------*/
