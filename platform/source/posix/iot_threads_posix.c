/*
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_threads_posix.c
 * @brief Implementation of the functions in iot_threads.h for POSIX systems.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdlib.h>

/* POSIX includes. Allow the default POSIX headers to be overridden. */
#ifdef POSIX_ERRNO_HEADER
    #include POSIX_ERRNO_HEADER
#else
    #include <errno.h>
#endif
#ifdef POSIX_LIMITS_HEADER
    #include POSIX_LIMITS_HEADER
#else
    #include <limits.h>
#endif
#ifdef POSIX_PTHREAD_HEADER
    #include POSIX_PTHREAD_HEADER
#else
    #include <pthread.h>
#endif
#ifdef POSIX_SEMAPHORE_HEADER
    #include POSIX_SEMAPHORE_HEADER
#else
    #include <semaphore.h>
#endif

/* Platform threads include. */
#include "platform/iot_threads.h"

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

/* When building tests, the Unity framework's malloc overrides are used to track
 * calls to platform resource creation and destruction. This ensures that all
 * platform resources are destroyed before the tests finish. When not testing,
 * define the Unity malloc functions to nothing. */
#if IOT_BUILD_TESTS != 1
    #define UnityMalloc_IncrementMallocCount()
    #define UnityMalloc_DecrementMallocCount()
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

/* Platform-specific function implemented in iot_clock_posix.c */
extern bool IotClock_TimeoutToTimespec( uint32_t timeoutMs,
                                        struct timespec * pOutput );

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
    else
    {
        /* Increment the number of platform resources in use. */
        UnityMalloc_IncrementMallocCount();
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
    /* Decrement the number of platform resources in use. */
    UnityMalloc_DecrementMallocCount();

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

    if( maxValue > ( uint32_t ) SEM_VALUE_MAX )
    {
        IotLogError( "%lu is larger than the maximum value a semaphore may"
                     " have on this system.", maxValue );

        status = false;
    }
    else
    {
        if( sem_init( pNewSemaphore, 0, ( unsigned int ) initialValue ) != 0 )
        {
            IotLogError( "Failed to create new semaphore %p. errno=%d.",
                         pNewSemaphore,
                         errno );

            status = false;
        }
        else
        {
            /* Increment the number of platform resources in use. */
            UnityMalloc_IncrementMallocCount();
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

uint32_t IotSemaphore_GetCount( IotSemaphore_t * pSemaphore )
{
    int count = 0;

    if( sem_getvalue( pSemaphore, &count ) != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to query semaphore count of %p. errno=%d.",
                     pSemaphore,
                     errno );

        abort();
    }

    return ( uint32_t ) count;
}

/*-----------------------------------------------------------*/

void IotSemaphore_Destroy( IotSemaphore_t * pSemaphore )
{
    /* Decrement the number of platform resources in use. */
    UnityMalloc_DecrementMallocCount();

    if( sem_destroy( pSemaphore ) != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to destroy semaphore %p. errno=%d.",
                     pSemaphore,
                     errno );

        abort();
    }
}

/*-----------------------------------------------------------*/

void IotSemaphore_Wait( IotSemaphore_t * pSemaphore )
{
    if( sem_wait( pSemaphore ) != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to wait on semaphore %p. errno=%d.",
                     pSemaphore,
                     errno );

        abort();
    }
}

/*-----------------------------------------------------------*/

bool IotSemaphore_TryWait( IotSemaphore_t * pSemaphore )
{
    bool status = true;

    if( sem_trywait( pSemaphore ) != 0 )
    {
        IotLogDebug( "Semaphore %p is not available. errno=%d.",
                     pSemaphore,
                     errno );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

bool IotSemaphore_TimedWait( IotSemaphore_t * pSemaphore,
                             uint32_t timeoutMs )
{
    bool status = true;
    struct timespec timeout = { 0 };

    if( IotClock_TimeoutToTimespec( timeoutMs, &timeout ) == false )
    {
        IotLogError( "Invalid timeout." );

        status = false;
    }
    else
    {
        if( sem_timedwait( pSemaphore, &timeout ) != 0 )
        {
            IotLogDebug( "Semaphore %p is not available. errno=%d.",
                         pSemaphore,
                         errno );

            status = false;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotSemaphore_Post( IotSemaphore_t * pSemaphore )
{
    if( sem_post( pSemaphore ) != 0 )
    {
        /* This block should not be reached; log an error and abort if it is. */
        IotLogError( "Failed to post to semaphore %p. errno=%d.",
                     pSemaphore,
                     errno );

        abort();
    }
}

/*-----------------------------------------------------------*/
