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
 * @file iot_threads_macos.c
 * @brief Implementation of the functions in iot_threads.h for macOS.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Error handling include. */
#include "private/iot_error.h"

/* Atomic include. */
#include "iot_atomic.h"

/* POSIX includes. Allow the default POSIX headers to be overridden. */
#ifdef POSIX_ERRNO_HEADER
    #include POSIX_ERRNO_HEADER
#else
    #include <errno.h>
#endif
#ifdef POSIX_PTHREAD_HEADER
    #include POSIX_PTHREAD_HEADER
#else
    #include <pthread.h>
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

#define LIBRARY_LOG_NAME    ( "THREAD" )
#include "iot_logging_setup.h"

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
 * @brief Wraps an #IotThreadRoutine_t with a POSIX-compliant one.
 *
 * @param[in] pArgument The value passed as `arg` to `pthread_create`.
 *
 * @return Always returns `NULL`.
 */
static void * _threadRoutineWrapper( void * pArgument );

/*-----------------------------------------------------------*/

static void * _threadRoutineWrapper( void * pArgument )
{
    _threadInfo_t * pThreadInfo = ( _threadInfo_t * ) pArgument;

    /* Read thread routine and argument, then free thread info. */
    IotThreadRoutine_t threadRoutine = pThreadInfo->threadRoutine;
    void * pThreadRoutineArgument = pThreadInfo->pArgument;

    IotThreads_Free( pThreadInfo );

    /* Run the thread routine. */
    threadRoutine( pThreadRoutineArgument );

    return NULL;
}

/*-----------------------------------------------------------*/

bool Iot_CreateDetachedThread( IotThreadRoutine_t threadRoutine,
                               void * pArgument,
                               int32_t priority,
                               size_t stackSize )
{
    IOT_FUNCTION_ENTRY( bool, true );
    int posixErrno = 0;
    bool threadAttibutesCreated = false;
    _threadInfo_t * pThreadInfo = NULL;
    pthread_t newThread;
    pthread_attr_t threadAttributes;

    /* Ignore priority and stack size. */
    ( void ) priority;
    ( void ) stackSize;

    /* Allocate memory for the new thread info. */
    pThreadInfo = IotThreads_Malloc( sizeof( _threadInfo_t ) );

    if( pThreadInfo == NULL )
    {
        IotLogError( "Failed to allocate memory for new thread." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Set up thread attributes object. */
    posixErrno = pthread_attr_init( &threadAttributes );

    if( posixErrno != 0 )
    {
        IotLogError( "Failed to initialize thread attributes. errno=%d.",
                     posixErrno );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    threadAttibutesCreated = true;

    /* Set the new thread to detached. */
    posixErrno = pthread_attr_setdetachstate( &threadAttributes,
                                              PTHREAD_CREATE_DETACHED );

    if( posixErrno != 0 )
    {
        IotLogError( "Failed to set detached thread attribute. errno=%d.",
                     posixErrno );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Set the thread routine and argument. */
    pThreadInfo->threadRoutine = threadRoutine;
    pThreadInfo->pArgument = pArgument;

    /* Create the underlying POSIX thread. */
    posixErrno = pthread_create( &newThread,
                                 &threadAttributes,
                                 _threadRoutineWrapper,
                                 pThreadInfo );

    if( posixErrno != 0 )
    {
        IotLogError( "Failed to create new thread. errno=%d.", posixErrno );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Destroy thread attributes object. */
    if( threadAttibutesCreated == true )
    {
        posixErrno = pthread_attr_destroy( &threadAttributes );

        if( posixErrno != 0 )
        {
            IotLogWarn( "Failed to destroy thread attributes. errno=%d.",
                        posixErrno );
        }
    }

    /* Clean up on error. */
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
    IOT_FUNCTION_ENTRY( bool, true );
    int mutexError = 0;
    pthread_mutexattr_t mutexAttributes, * pMutexAttributes = NULL;

    if( recursive == true )
    {
        /* Create new mutex attributes object. */
        mutexError = pthread_mutexattr_init( &mutexAttributes );

        if( mutexError != 0 )
        {
            IotLogError( "Failed to initialize mutex attributes. errno=%d.",
                         mutexError );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }

        pMutexAttributes = &mutexAttributes;

        /* Set recursive mutex type. */
        mutexError = pthread_mutexattr_settype( &mutexAttributes,
                                                PTHREAD_MUTEX_RECURSIVE );

        if( mutexError != 0 )
        {
            IotLogError( "Failed to set recursive mutex type. errno=%d.",
                         mutexError );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    }

    mutexError = pthread_mutex_init( pNewMutex, pMutexAttributes );

    if( mutexError != 0 )
    {
        IotLogError( "Failed to create new mutex %p. errno=%d.",
                     pNewMutex,
                     mutexError );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Destroy any created mutex attributes. */
    if( pMutexAttributes != NULL )
    {
        ( void ) pthread_mutexattr_destroy( &mutexAttributes );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

void IotMutex_Destroy( IotMutex_t * pMutex )
{
    int mutexError = pthread_mutex_destroy( pMutex );

    if( mutexError != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to destroy mutex %p. errno=%d.",
                     pMutex,
                     mutexError );

        abort();
    }
}

/*-----------------------------------------------------------*/

void IotMutex_Lock( IotMutex_t * pMutex )
{
    int mutexError = pthread_mutex_lock( pMutex );

    if( mutexError != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to lock mutex %p. errno=%d.",
                     pMutex,
                     mutexError );

        abort();
    }
}

/*-----------------------------------------------------------*/

bool IotMutex_TryLock( IotMutex_t * pMutex )
{
    bool status = true;
    int mutexError = pthread_mutex_trylock( pMutex );

    if( mutexError != 0 )
    {
        IotLogDebug( "Mutex mutex %p is not available. errno=%d.",
                     pMutex,
                     mutexError );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotMutex_Unlock( IotMutex_t * pMutex )
{
    int mutexError = pthread_mutex_unlock( pMutex );

    if( mutexError != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to unlock mutex %p. errno=%d.",
                     pMutex,
                     mutexError );

        abort();
    }
}

/*-----------------------------------------------------------*/

bool IotSemaphore_Create( IotSemaphore_t * pNewSemaphore,
                          uint32_t initialValue,
                          uint32_t maxValue )
{
    bool status = true;

    /* Create a GCD semaphore. */
    pNewSemaphore->semaphore = dispatch_semaphore_create( ( long ) initialValue );

    if( pNewSemaphore->semaphore == NULL )
    {
        IotLogError( "Failed to create new dispatch semaphore." );
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
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/platform/platform_threads_function_semaphoredestroy.html
     */
}

/*-----------------------------------------------------------*/

uint32_t IotSemaphore_GetCount( IotSemaphore_t * pSemaphore )
{
    return Atomic_Add_u32( &( pSemaphore->count ), 0 );
}

/*-----------------------------------------------------------*/

void IotSemaphore_Wait( IotSemaphore_t * pSemaphore )
{
    long dispatchError = dispatch_semaphore_wait( pSemaphore->semaphore,
                                                  DISPATCH_TIME_FOREVER );

    /* Waiting forever for a valid semaphore should not fail. */
    if( dispatchError != 0 )
    {
        IotLogError( "(Semaphore %p) Failed to wait on dispatch semaphore, returned %ld.",
                     pSemaphore,
                     dispatchError );

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
    bool status = true;

    /* Convert timeoutMs to nanoseconds. */
    int64_t delta = ( int64_t ) timeoutMs * 1000000LL;

    /* Create a dispatch time representation representing the timeout. */
    dispatch_time_t timeout = dispatch_time( DISPATCH_TIME_NOW,
                                             delta );

    /* Wait on the dispatch semaphore with a timeout. */
    long dispatchError = dispatch_semaphore_wait( pSemaphore->semaphore,
                                                  timeout );

    if( dispatchError == 0 )
    {
        if( Atomic_Decrement_u32( &( pSemaphore->count ) ) == 0 )
        {
            IotLogError( "(Semaphore %p) Semaphore count decremented beyond 0.", pSemaphore );

            abort();
        }
    }
    else
    {
        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotSemaphore_Post( IotSemaphore_t * pSemaphore )
{
    Atomic_Increment_u32( &( pSemaphore->count ) );

    /* Signal dispatch semaphore. The return value (whether a thread was woken)
     * is ignored. */
    ( void ) dispatch_semaphore_signal( pSemaphore->semaphore );
}

/*-----------------------------------------------------------*/
