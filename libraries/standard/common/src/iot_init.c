/*
 * IoT Common V1.1.0
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
 * @file iot_init.c
 * @brief Implements functions for common intialization and cleanup of this SDK.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Task pool include. */
#include "iot_taskpool.h"

/* Atomic include. */
#include "iot_atomic.h"

/* Static memory include (if dynamic memory allocation is disabled). */
#include "iot_static_memory.h"

/* Error handling include. */
#include "iot_error.h"

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_GLOBAL
    #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
#else
    #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
#endif

#define LIBRARY_LOG_NAME         ( "INIT" )
#include "iot_logging_setup.h"

/*-----------------------------------------------------------*/

/* A mutex for critical sections is needed for the generic atomic implementation. */
#if ( IOT_ATOMIC_GENERIC == 1 )
    /* Platform threads include. */
    #include "platform/iot_threads.h"

/**
 * @brief Provides critical sections.
 */
    static IotMutex_t _atomicMutex;

/*-----------------------------------------------------------*/

    void Iot_EnterCritical( void )
    {
        IotMutex_Lock( &_atomicMutex );
    }

/*-----------------------------------------------------------*/

    void Iot_ExitCritical( void )
    {
        IotMutex_Unlock( &_atomicMutex );
    }

#endif /* if ( IOT_ATOMIC_GENERIC == 1 ) */

/*-----------------------------------------------------------*/

bool IotSdk_Init( void )
{
    IOT_FUNCTION_ENTRY( bool, true );
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    IotTaskPoolInfo_t taskPoolInfo = IOT_TASKPOOL_INFO_INITIALIZER_LARGE;

    /* Initialize the mutex for atomic operations if needed. */
    #if ( IOT_ATOMIC_GENERIC == 1 )
        bool atomicInitialized = IotMutex_Create( &_atomicMutex, false );

        if( atomicInitialized == false )
        {
            IotLogError( "Failed to initialize atomic operations." );
            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    #endif

    /* Create system task pool. */
    taskPoolStatus = IotTaskPool_CreateSystemTaskPool( &taskPoolInfo );

    if( taskPoolStatus != IOT_TASKPOOL_SUCCESS )
    {
        IotLogError( "Failed to create system task pool." );
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status == false )
    {
        #if IOT_ATOMIC_GENERIC == 1
            if( atomicInitialized == true )
            {
                IotMutex_Destroy( &_atomicMutex );
            }
        #endif
    }
    else
    {
        IotLogInfo( "SDK successfully initialized." );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

void IotSdk_Cleanup( void )
{
    IotTaskPool_Destroy( IOT_SYSTEM_TASKPOOL );

    /* This log message must be printed before static memory management is
     * cleaned up. */
    IotLogInfo( "SDK cleanup done." );

    /* Clean up the mutex for generic atomic operations if needed. */
    #if ( IOT_ATOMIC_GENERIC == 1 )
        IotMutex_Destroy( &_atomicMutex );
    #endif
}

/*-----------------------------------------------------------*/
