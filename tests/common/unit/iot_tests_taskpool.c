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
 * @file iot_tests_taskpool.c
 * @brief Tests for task pool.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* POSIX includes. */
#include <time.h>

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* MQTT internal include. */
#include "private/iot_taskpool_internal.h"

/* Task pool include. */
#include "iot_taskpool.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief A simple user context to prove all callbacks are called.
 */
typedef struct JobUserContext
{
    IotMutex_t lock;  /**< @brief Protection from concurrent updates. */
    uint32_t counter; /**< @brief A counter to keep track of callback invokations. */
} JobUserContext_t;

/**
 * @brief A simple user context to prove the taskpool grows as expected.
 */
typedef struct JobBlockingUserContext
{
    IotSemaphore_t signal; /**< @brief A synch object to signal. */
    IotSemaphore_t block;  /**< @brief A synch object to wait on. */
} JobBlockingUserContext_t;

/*-----------------------------------------------------------*/

/**
 * @brief Test group for task pool tests.
 */
TEST_GROUP( Common_Unit_Task_Pool );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for task pool tests.
 */
TEST_SETUP( Common_Unit_Task_Pool )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for task pool tests.
 */
TEST_TEAR_DOWN( Common_Unit_Task_Pool )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for task pool.
 */
TEST_GROUP_RUNNER( Common_Unit_Task_Pool )
{
    RUN_TEST_CASE( Common_Unit_Task_Pool, CreateDestroy );
    RUN_TEST_CASE( Common_Unit_Task_Pool, CreateJobError );
    RUN_TEST_CASE( Common_Unit_Task_Pool, CreateRecyclableJob );
    RUN_TEST_CASE( Common_Unit_Task_Pool, ScheduleTasksError );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_Grow );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleOneThenWait );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleOneDeferredThenWait );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleAllThenWait );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleAllRecyclableThenWait );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleAllDeferredRecyclableThenWait );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ReSchedule );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ReScheduleDeferred );
    RUN_TEST_CASE( Common_Unit_Task_Pool, TaskPool_CancelTasks );
}

/*-----------------------------------------------------------*/

/**
 * @brief Number of iterations for each test loop.
 */
#ifndef _TASKPOOL_TEST_ITERATIONS
    #define _TASKPOOL_TEST_ITERATIONS    ( 200 )
#endif

/**
 * @brief Define the stress job max duration time (emulated duration).
 */
#ifndef _TASKPOOL_TEST_WORK_ITEM_DURATION_MAX
    #define _TASKPOOL_TEST_WORK_ITEM_DURATION_MAX    ( 55 )
#endif

/**
 * @brief A global delay to wait for threads to exit or such...
 */
static struct itimerspec _TEST_DELAY_50MS =
{
    .it_value.tv_sec  = 0,
    .it_value.tv_nsec = ( 50000000L ), /* 50ms */
    .it_interval      = { 0 }
};

/* ---------------------------------------------------------- */

/**
 * @brief A function that emulates some work in the task pool execution by sleeping.
 */
static void EmulateWork()
{
    int32_t duration_in_nsec = ( ( 1000000 ) * ( rand() % _TASKPOOL_TEST_WORK_ITEM_DURATION_MAX ) );

    TEST_ASSERT_TRUE( duration_in_nsec <= 999999999 );

    struct timespec delay =
    {
        .tv_sec  = 0,
        .tv_nsec = duration_in_nsec
    };

    int error = clock_nanosleep( CLOCK_MONOTONIC, 0, &delay, NULL );

    TEST_ASSERT_TRUE( error == 0 );
}

/**
 * @brief A function that emulates some work in the task pool execution by sleeping.
 */
static void EmulateWorkLong()
{
    int32_t duration_in_nsec = ( ( 1000000 ) * ( rand() % _TASKPOOL_TEST_WORK_ITEM_DURATION_MAX ) );

    TEST_ASSERT_TRUE( duration_in_nsec <= 999999999 );

    /* Emulate at least 10 seconds worth of work. */
    struct timespec delay =
    {
        .tv_sec  = 2,
        .tv_nsec = duration_in_nsec
    };

    int error = clock_nanosleep( CLOCK_MONOTONIC, 0, &delay, NULL );

    TEST_ASSERT_TRUE( error == 0 );
}

/**
 * @brief A callback that recycles its job.
 */
static void ExecutionWithDestroyCb( IotTaskPool_t * pTaskPool,
                                    IotTaskPoolJob_t * pJob,
                                    void * context )
{
    JobUserContext_t * pUserContext;
    IotTaskPoolJobStatus_t status;

    TEST_ASSERT( IotLink_IsLinked( &pJob->link ) == false );

    TEST_ASSERT( IotTaskPool_GetStatus( pTaskPool, pJob, &status ) == IOT_TASKPOOL_SUCCESS );
    TEST_ASSERT( status == IOT_TASKPOOL_STATUS_EXECUTING );

    EmulateWork();

    pUserContext = ( JobUserContext_t * ) context;

    IotMutex_Lock( &pUserContext->lock );
    pUserContext->counter++;
    IotMutex_Unlock( &pUserContext->lock );

    TEST_ASSERT( IotTaskPool_DestroyJob( pTaskPool, pJob ) == IOT_TASKPOOL_SUCCESS );
}

/**
 * @brief A callback that does not recycle its job.
 */
static void ExecutionWithoutDestroyCb( IotTaskPool_t * pTaskPool,
                                       IotTaskPoolJob_t * pJob,
                                       void * context )
{
    JobUserContext_t * pUserContext;
    IotTaskPoolJobStatus_t status;

    TEST_ASSERT( IotLink_IsLinked( &pJob->link ) == false );

    TEST_ASSERT( IotTaskPool_GetStatus( pTaskPool, pJob, &status ) == IOT_TASKPOOL_SUCCESS );
    TEST_ASSERT( status == IOT_TASKPOOL_STATUS_EXECUTING );

    EmulateWork();

    pUserContext = ( JobUserContext_t * ) context;

    IotMutex_Lock( &pUserContext->lock );
    pUserContext->counter++;
    IotMutex_Unlock( &pUserContext->lock );
}

/**
 * @brief A callback that blocks.
 */
static void ExecutionBlockingWithoutDestroyCb( IotTaskPool_t * pTaskPool,
                                               IotTaskPoolJob_t * pJob,
                                               void * context )
{
    JobBlockingUserContext_t * pUserContext;
    IotTaskPoolJobStatus_t status;

    TEST_ASSERT( IotLink_IsLinked( &pJob->link ) == false );

    TEST_ASSERT( IotTaskPool_GetStatus( pTaskPool, pJob, &status ) == IOT_TASKPOOL_SUCCESS );
    TEST_ASSERT( status == IOT_TASKPOOL_STATUS_EXECUTING );

    pUserContext = ( JobBlockingUserContext_t * ) context;

    /* Signal that the vallback has been called. */
    IotSemaphore_Post( &pUserContext->signal );

    /* This callback will emulate a blocking wait, for the sole purpose of stealing a task pool
     * thread and test that the taskpool can actually grow as expected. */
    IotSemaphore_Wait( &pUserContext->block );
}

/**
 * @brief A callback that recycles its job.
 */
static void ExecutionWithRecycleCb( IotTaskPool_t * pTaskPool,
                                    IotTaskPoolJob_t * pJob,
                                    void * context )
{
    JobUserContext_t * pUserContext;
    IotTaskPoolJobStatus_t status;

    TEST_ASSERT( IotLink_IsLinked( &pJob->link ) == false );

    TEST_ASSERT( IotTaskPool_GetStatus( pTaskPool, pJob, &status ) == IOT_TASKPOOL_SUCCESS );
    TEST_ASSERT( status == IOT_TASKPOOL_STATUS_EXECUTING );

    EmulateWork();

    pUserContext = ( JobUserContext_t * ) context;

    IotMutex_Lock( &pUserContext->lock );
    pUserContext->counter++;
    IotMutex_Unlock( &pUserContext->lock );

    IotTaskPool_RecycleJob( pTaskPool, pJob );
}

/**
 * @brief A callback that takes a long time and does not recycle its job.
 */
static void ExecutionLongWithoutDestroyCb( IotTaskPool_t * pTaskPool,
                                           IotTaskPoolJob_t * pJob,
                                           void * context )
{
    JobUserContext_t * pUserContext;
    IotTaskPoolJobStatus_t status;

    TEST_ASSERT( IotLink_IsLinked( &pJob->link ) == false );

    TEST_ASSERT( IotTaskPool_GetStatus( pTaskPool, pJob, &status ) == IOT_TASKPOOL_SUCCESS );
    TEST_ASSERT( status == IOT_TASKPOOL_STATUS_EXECUTING );

    EmulateWorkLong();

    pUserContext = ( JobUserContext_t * ) context;

    IotMutex_Lock( &pUserContext->lock );
    pUserContext->counter++;
    IotMutex_Unlock( &pUserContext->lock );
}

/* ---------------------------------------------------------------------------------------------- */
/* ---------------------------------------------------------------------------------------------- */
/* ---------------------------------------------------------------------------------------------- */

/**
 * @brief Number of legal task pool initialization configurations.
 */
#define LEGAL_INFOS      3

/**
 * @brief Number of illegal task pool initialization configurations.
 */
#define ILLEGAL_INFOS    3

/**
 * @brief Legal initialization configurations.
 */
IotTaskPoolInfo_t tpInfoLegal[ LEGAL_INFOS ] =
{
    { .minThreads = 1, .maxThreads = 1, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY },
    { .minThreads = 1, .maxThreads = 2, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY },
    { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY }
};

/**
 * @brief Illegal initialization configurations.
 */
IotTaskPoolInfo_t tpInfoIllegal[ ILLEGAL_INFOS ] =
{
    { .minThreads = 0, .maxThreads = 1, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY },
    { .minThreads = 1, .maxThreads = 0, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY },
    { .minThreads = 2, .maxThreads = 1, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY }
};

/*-----------------------------------------------------------*/

/**
 * @brief Test task pool dynamic memory creation and destruction, with both legal and illegal information.
 */
TEST( Common_Unit_Task_Pool, CreateDestroy )
{
    uint32_t count;
    IotTaskPool_t taskPool;

    for( count = 0; count < LEGAL_INFOS; ++count )
    {
        TEST_ASSERT( IotTaskPool_Create( &tpInfoLegal[ count ], &taskPool ) == IOT_TASKPOOL_SUCCESS );
        TEST_ASSERT( IotTaskPool_Destroy( &taskPool ) == IOT_TASKPOOL_SUCCESS );
    }

    for( count = 0; count < ILLEGAL_INFOS; ++count )
    {
        TEST_ASSERT( IotTaskPool_Create( &tpInfoIllegal[ count ], &taskPool ) == IOT_TASKPOOL_BAD_PARAMETER );
    }

    TEST_ASSERT( IotTaskPool_Create( &tpInfoLegal[ 0 ], NULL ) == IOT_TASKPOOL_BAD_PARAMETER );
    TEST_ASSERT( IotTaskPool_Create( NULL, &taskPool ) == IOT_TASKPOOL_BAD_PARAMETER );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test task pool job static and dynamic memory creation with bogus parameters.
 */
TEST( Common_Unit_Task_Pool, CreateJobError )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Non-recyclable jobs. */
    {
        IotTaskPoolJob_t job;

        /* NULL callback. */
        TEST_ASSERT( IotTaskPool_CreateJob( NULL, NULL, &job ) == IOT_TASKPOOL_BAD_PARAMETER );
        /* NULL job handle. */
        TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionWithDestroyCb, NULL, NULL ) == IOT_TASKPOOL_BAD_PARAMETER );
    }

    /* Recyclable jobs. */
    {
        IotTaskPoolJob_t * pJob = NULL;
        /* NULL callback. */
        TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, NULL, NULL, &pJob ) == IOT_TASKPOOL_BAD_PARAMETER );
        /* NULL engine handle. */
        TEST_ASSERT( IotTaskPool_CreateRecyclableJob( NULL, &ExecutionWithRecycleCb, NULL, &pJob ) == IOT_TASKPOOL_BAD_PARAMETER );
        /* NULL job handle. */
        TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, &ExecutionWithRecycleCb, NULL, NULL ) == IOT_TASKPOOL_BAD_PARAMETER );
    }

    IotTaskPool_Destroy( &taskPool );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test task pool job static and dynamic memory creation with bogus parameters.
 */
TEST( Common_Unit_Task_Pool, CreateRecyclableJob )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Recyclable jobs. */
    {
        uint32_t count, jobLimit;

        /* In static memory mode, only the recyclable job limit may be allocated. */
        #if IOT_STATIC_MEMORY_ONLY == 1
            jobLimit = IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
            IotTaskPoolJob_t * pJobs[ IOT_TASKPOOL_JOBS_RECYCLE_LIMIT ] = { 0 };
        #else
            jobLimit = 2 * IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
            IotTaskPoolJob_t * pJobs[ 2 * _TASKPOOL_TEST_ITERATIONS ] = { 0 };
        #endif

        for( count = 0; count < jobLimit; ++count )
        {
            TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, &ExecutionWithRecycleCb, NULL, &pJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );
            TEST_ASSERT( pJobs[ count ] != NULL );
        }

        for( count = 0; count < jobLimit; ++count )
        {
            TEST_ASSERT( IotTaskPool_RecycleJob( &taskPool, pJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );
        }
    }

    IotTaskPool_Destroy( &taskPool );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a job with bad parameters.
 */
TEST( Common_Unit_Task_Pool, ScheduleTasksError )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    IotTaskPool_Create( &tpInfo, &taskPool );

    IotTaskPoolJob_t job;

    TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionWithDestroyCb, NULL, &job ) == IOT_TASKPOOL_SUCCESS );

    /* NULL Task Pool Handle. */
    TEST_ASSERT( IotTaskPool_Schedule( NULL, &job ) == IOT_TASKPOOL_BAD_PARAMETER );
    /* NULL Work item Handle. */
    TEST_ASSERT( IotTaskPool_Schedule( &taskPool, NULL ) == IOT_TASKPOOL_BAD_PARAMETER );
    /* Destroy the job, so we do not leak it. */
    TEST_ASSERT( IotTaskPool_DestroyJob( &taskPool, &job ) == IOT_TASKPOOL_SUCCESS );

    IotTaskPool_Destroy( &taskPool );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a job with bad parameters.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleRecyclableTasksError )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    IotTaskPool_Create( &tpInfo, &taskPool );

    IotTaskPoolJob_t * pJob;

    TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, &ExecutionWithRecycleCb, NULL, &pJob ) == IOT_TASKPOOL_SUCCESS );

    /* NULL Task Pool Handle. */
    TEST_ASSERT( IotTaskPool_Schedule( NULL, pJob ) == IOT_TASKPOOL_BAD_PARAMETER );
    /* NULL Work item Handle. */
    TEST_ASSERT( IotTaskPool_Schedule( &taskPool, NULL ) == IOT_TASKPOOL_BAD_PARAMETER );
    /* Recycle the job, so we do not leak it. */
    TEST_ASSERT( IotTaskPool_RecycleJob( &taskPool, pJob ) == IOT_TASKPOOL_SUCCESS );

    IotTaskPool_Destroy( &taskPool );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that the taskpool actually grows the number of tasks as expected.
 */
TEST( Common_Unit_Task_Pool, TaskPool_Grow )
{
#define _NUMBER_OF_JOBS    4

    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = _NUMBER_OF_JOBS, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobBlockingUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotSemaphore_Create( &userContext.signal, 0, _NUMBER_OF_JOBS ) );
    TEST_ASSERT( IotSemaphore_Create( &userContext.block, 0, _NUMBER_OF_JOBS ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated job, schedule one, then wait. */
    {
        uint32_t count;
        IotTaskPoolJob_t jobs[ _NUMBER_OF_JOBS ];

        /* Create a number of jobs that is equal to the max number of threads in the taskpool. */
        for( count = 0; count < _NUMBER_OF_JOBS; ++count )
        {
            /* Shedule the job NOT to be recycle in the callback, since the buffer is statically allocated. */
            /* The callback will block indefintely, stealing a task pool thread. The task pool will need to grow to pass this test. */
            TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionBlockingWithoutDestroyCb, &userContext, &jobs[ count ] ) == IOT_TASKPOOL_SUCCESS );
        }

        for( count = 0; count < _NUMBER_OF_JOBS; ++count )
        {
            TEST_ASSERT( IotTaskPool_Schedule( &taskPool, &jobs[ count ] ) == IOT_TASKPOOL_SUCCESS );
        }

        count = 0;

        while( true )
        {
            /* Wait for the callback to signal the semaphore. It must happen exactly _NUMBER_OF_JOBS times. */
            IotSemaphore_Wait( &userContext.signal );

            ++count;

            if( count == _NUMBER_OF_JOBS )
            {
                break;
            }
        }

        /* Signal all taskpool threads to exit. */
        for( count = 0; count < _NUMBER_OF_JOBS; ++count )
        {
            IotSemaphore_Post( &userContext.block );
        }
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotSemaphore_Destroy( &userContext.signal );
    IotSemaphore_Destroy( &userContext.block );

#undef _NUMBER_OF_JOBS
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a set of non-recyclable jobs: static allocation, sequential execution.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleOneThenWait )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated job, schedule one, then wait. */
    {
        uint32_t count;
        uint32_t scheduled = 0;
        IotTaskPoolJob_t job;

        for( count = 0; count < _TASKPOOL_TEST_ITERATIONS; ++count )
        {
            /* Shedule the job NOT to be recycle in the callback, since the buffer is statically allocated. */
            TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionWithoutDestroyCb, &userContext, &job ) == IOT_TASKPOOL_SUCCESS );

            IotTaskPoolError_t errorSchedule = IotTaskPool_Schedule( &taskPool, &job );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                    TEST_ASSERT( false );
                    break;

                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    TEST_ASSERT( false );
                    break;

                case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }

            /* Ensure callback actually executed. */
            while( true )
            {
                ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

                IotMutex_Lock( &userContext.lock );

                if( userContext.counter == scheduled )
                {
                    IotMutex_Unlock( &userContext.lock );

                    break;
                }

                IotMutex_Unlock( &userContext.lock );
            }

            TEST_ASSERT( userContext.counter == scheduled );

            TEST_ASSERT( IotTaskPool_DestroyJob( &taskPool, &job ) == IOT_TASKPOOL_SUCCESS );
        }

        /* Since jobs were build from a static buffer and scheduled one-by-one, we
         * should have received all callbacks.
         */
        TEST_ASSERT( scheduled == _TASKPOOL_TEST_ITERATIONS );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a set of non-recyclable jobs: static allocation, sequential execution.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleOneDeferredThenWait )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated job, schedule one, then wait. */
    {
        uint32_t count;
        uint32_t scheduled = 0;
        IotTaskPoolJob_t job;

        for( count = 0; count < _TASKPOOL_TEST_ITERATIONS; ++count )
        {
            /* Shedule the job NOT to be recycle in the callback, since the buffer is statically allocated. */
            TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionWithoutDestroyCb, &userContext, &job ) == IOT_TASKPOOL_SUCCESS );

            IotTaskPoolError_t errorSchedule = IotTaskPool_ScheduleDeferred( &taskPool, &job, 10 + ( rand() % 50 ) );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                    TEST_ASSERT( false );
                    break;

                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    TEST_ASSERT( false );
                    break;

                case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }

            /* Ensure callback actually executed. */
            while( true )
            {
                ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

                IotMutex_Lock( &userContext.lock );

                if( userContext.counter == scheduled )
                {
                    IotMutex_Unlock( &userContext.lock );

                    break;
                }

                IotMutex_Unlock( &userContext.lock );
            }

            TEST_ASSERT( userContext.counter == scheduled );

            TEST_ASSERT( IotTaskPool_DestroyJob( &taskPool, &job ) == IOT_TASKPOOL_SUCCESS );
        }

        /* Since jobs were build from a static buffer and scheduled one-by-one, we
         * should have received all callbacks.
         */
        TEST_ASSERT( scheduled == _TASKPOOL_TEST_ITERATIONS );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a set of recyclable jobs: dynamic allocation, sequential execution.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleOneRecyclableThenWait )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Dynamically allocated job, schedule one, then wait. */
    {
        uint32_t count;
        uint32_t scheduled = 0;
        IotTaskPoolJob_t * pJob;

        for( count = 0; count < _TASKPOOL_TEST_ITERATIONS; ++count )
        {
            /* Shedule the job to be recycle in the callback. */
            TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, &ExecutionWithRecycleCb, &userContext, &pJob ) == IOT_TASKPOOL_SUCCESS );

            IotTaskPoolError_t errorSchedule = IotTaskPool_Schedule( &taskPool, pJob );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }

            /* Ensure callback actually executed. */
            while( true )
            {
                ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

                IotMutex_Lock( &userContext.lock );

                if( userContext.counter == scheduled )
                {
                    IotMutex_Unlock( &userContext.lock );

                    break;
                }

                IotMutex_Unlock( &userContext.lock );
            }

            TEST_ASSERT( userContext.counter == scheduled );
        }

        TEST_ASSERT( scheduled == _TASKPOOL_TEST_ITERATIONS );

        /* Since jobs were build from a static buffer and scheduled one-by-one, we
         * should have received all callbacks.
         */
        TEST_ASSERT( scheduled == _TASKPOOL_TEST_ITERATIONS );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a set of jobs: static allocation, bulk execution.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleAllThenWait )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated jobs, schedule all, then wait all. */
    {
        uint32_t count;
        uint32_t scheduled = 0;
        IotTaskPoolJob_t tpJobs[ _TASKPOOL_TEST_ITERATIONS ] = { { 0 } };

        for( count = 0; count < _TASKPOOL_TEST_ITERATIONS; ++count )
        {
            /* Shedule the job NOT to be recycle in the callback, since the buffer is statically allocated. */
            TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionWithoutDestroyCb, &userContext, &tpJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );

            IotTaskPoolError_t errorSchedule = IotTaskPool_Schedule( &taskPool, &tpJobs[ count ] );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        /* Wait until callback is executed. */
        while( true )
        {
            ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

            IotMutex_Lock( &userContext.lock );

            if( userContext.counter == scheduled )
            {
                IotMutex_Unlock( &userContext.lock );

                break;
            }

            IotMutex_Unlock( &userContext.lock );
        }

        TEST_ASSERT_TRUE( userContext.counter == scheduled );

        for( count = 0; count < _TASKPOOL_TEST_ITERATIONS; ++count )
        {
            TEST_ASSERT( IotTaskPool_DestroyJob( &taskPool, &tpJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );
        }
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}
/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a set of jobs: static allocation, bulk execution.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleAllRecyclableThenWait )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated jobs, schedule all, then wait all. */
    {
        uint32_t count, maxJobs;
        uint32_t scheduled = 0;

        /* In static memory mode, only the recyclable job limit may be allocated. */
        #if IOT_STATIC_MEMORY_ONLY == 1
            maxJobs = IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
            IotTaskPoolJob_t * tpJobs[ IOT_TASKPOOL_JOBS_RECYCLE_LIMIT ] = { 0 };
        #else
            maxJobs = _TASKPOOL_TEST_ITERATIONS;
            IotTaskPoolJob_t * tpJobs[ _TASKPOOL_TEST_ITERATIONS ] = { 0 };
        #endif

        for( count = 0; count < maxJobs; ++count )
        {
            /* Shedule the job to be recycle in the callback. */
            TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, &ExecutionWithRecycleCb, &userContext, &tpJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );

            IotTaskPoolError_t errorSchedule = IotTaskPool_Schedule( &taskPool, tpJobs[ count ] );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        /* Wait until callback is executed. */
        while( true )
        {
            ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

            IotMutex_Lock( &userContext.lock );

            if( userContext.counter == scheduled )
            {
                IotMutex_Unlock( &userContext.lock );

                break;
            }

            IotMutex_Unlock( &userContext.lock );
        }

        TEST_ASSERT_TRUE( userContext.counter == scheduled );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling a set of deferred jobs.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ScheduleAllDeferredRecyclableThenWait )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated jobs, schedule all, then wait all. */
    {
        uint32_t count, maxJobs;
        uint32_t scheduled = 0;

        /* In static memory mode, only the recyclable job limit may be allocated. */
        #if IOT_STATIC_MEMORY_ONLY == 1
            maxJobs = IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
            IotTaskPoolJob_t * tpJobs[ IOT_TASKPOOL_JOBS_RECYCLE_LIMIT ] = { 0 };
        #else
            maxJobs = _TASKPOOL_TEST_ITERATIONS;
            IotTaskPoolJob_t * tpJobs[ _TASKPOOL_TEST_ITERATIONS ] = { 0 };
        #endif

        for( count = 0; count < maxJobs; ++count )
        {
            /* Shedule the job to be recycle in the callback. */
            TEST_ASSERT( IotTaskPool_CreateRecyclableJob( &taskPool, &ExecutionWithRecycleCb, &userContext, &tpJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );

            IotTaskPoolError_t errorSchedule = IotTaskPool_ScheduleDeferred( &taskPool, tpJobs[ count ], 10 + ( rand() % 500 ) );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        /* Wait until callback is executed. */
        while( true )
        {
            ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

            IotMutex_Lock( &userContext.lock );

            if( userContext.counter == scheduled )
            {
                IotMutex_Unlock( &userContext.lock );

                break;
            }

            IotMutex_Unlock( &userContext.lock );
        }

        TEST_ASSERT_TRUE( userContext.counter == scheduled );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling and re-scheduling (without canceling first) a set of jobs.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ReSchedule )
{
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated jobs, schedule all, then wait all. */
    {
        uint32_t count, maxJobs;
        uint32_t scheduled = 0, rescheduled = 0, failedReschudule = 0;

        /* In static memory mode, only the recyclable job limit may be allocated. */
        #if IOT_STATIC_MEMORY_ONLY == 1
            maxJobs = IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
            IotTaskPoolJob_t tpJobs[ IOT_TASKPOOL_JOBS_RECYCLE_LIMIT ] = { 0 };
        #else
            maxJobs = 10;
            IotTaskPoolJob_t tpJobs[ 10 ] = { 0 };
        #endif

        /* Create all jobs. */
        for( count = 0; count < maxJobs; ++count )
        {
            /* Shedule the job to be recycled in the callback. */
            TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionLongWithoutDestroyCb, &userContext, &tpJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );
        }

        /* Schedule all jobs. */
        for( count = 0; count < maxJobs; ++count )
        {
            IotTaskPoolError_t errorSchedule;

            /* Schedule jobs for a really really long time from now, so we know that they will not execute. */
            errorSchedule = IotTaskPool_Schedule( &taskPool, &tpJobs[ count ] );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        /* Give a chance to some jobs to start execution. */
        ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

        /* Reschedule all. Some will fail to be rescheduled... */
        for( count = 0; count < maxJobs; ++count )
        {
            IotTaskPoolError_t errorReSchedule;

            errorReSchedule = IotTaskPool_Schedule( &taskPool, &tpJobs[ count ] );

            switch( errorReSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    rescheduled++;
                    break;

                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    /* Job already executed. */
                    failedReschudule++;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        TEST_ASSERT_TRUE( ( rescheduled + failedReschudule ) == scheduled );

        /* Wait until callback is executed. */
        while( true )
        {
            ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

            IotMutex_Lock( &userContext.lock );

            if( userContext.counter == scheduled )
            {
                IotMutex_Unlock( &userContext.lock );

                break;
            }

            IotMutex_Unlock( &userContext.lock );
        }

        TEST_ASSERT_TRUE( userContext.counter == scheduled );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling and re-scheduling (without canceling first) a set of deferred jobs.
 */
TEST( Common_Unit_Task_Pool, TaskPool_ScheduleTasks_ReScheduleDeferred )
{
#define _ONE_HOUR_IN_MS    ( 60 * 60 * 1000 )

    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };

    JobUserContext_t userContext = { 0 };

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Statically allocated jobs, schedule all, then wait all. */
    {
        uint32_t count, maxJobs;
        uint32_t scheduled = 0, rescheduled = 0;

        /* In static memory mode, only the recyclable job limit may be allocated. */
        #if IOT_STATIC_MEMORY_ONLY == 1
            maxJobs = IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
            IotTaskPoolJob_t tpJobs[ IOT_TASKPOOL_JOBS_RECYCLE_LIMIT ] = { 0 };
        #else
            maxJobs = _TASKPOOL_TEST_ITERATIONS;
            IotTaskPoolJob_t tpJobs[ _TASKPOOL_TEST_ITERATIONS ] = { 0 };
        #endif

        /* Schedule all jobs. */
        for( count = 0; count < maxJobs; ++count )
        {
            IotTaskPoolError_t errorSchedule;

            /* Shedule the job to be recycle in the callback. */
            TEST_ASSERT( IotTaskPool_CreateJob( &ExecutionWithoutDestroyCb, &userContext, &tpJobs[ count ] ) == IOT_TASKPOOL_SUCCESS );

            /* Schedule jobs for a really really long time from now, so we know that they will not execute. */
            errorSchedule = IotTaskPool_ScheduleDeferred( &taskPool, &tpJobs[ count ], _ONE_HOUR_IN_MS );

            switch( errorSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++scheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        /* Reschedule all. */
        for( count = 0; count < maxJobs; ++count )
        {
            IotTaskPoolError_t errorReSchedule;

            errorReSchedule = IotTaskPool_ScheduleDeferred( &taskPool, &tpJobs[ count ], 10 + ( rand() % 500 ) );

            switch( errorReSchedule )
            {
                case IOT_TASKPOOL_SUCCESS:
                    ++rescheduled;
                    break;

                case IOT_TASKPOOL_BAD_PARAMETER:
                case IOT_TASKPOOL_ILLEGAL_OPERATION:
                case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                    TEST_ASSERT( false );
                    break;

                default:
                    TEST_ASSERT( false );
            }
        }

        TEST_ASSERT_TRUE( rescheduled == scheduled );

        /* Wait until callback is executed. */
        while( true )
        {
            ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );

            IotMutex_Lock( &userContext.lock );

            if( userContext.counter == scheduled )
            {
                IotMutex_Unlock( &userContext.lock );

                break;
            }

            IotMutex_Unlock( &userContext.lock );
        }

        TEST_ASSERT_TRUE( userContext.counter == scheduled );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );

#undef _ONE_HOUR_IN_MS
}

/*-----------------------------------------------------------*/

/**
 * @brief Test scheduling and canceling jobs.
 */
TEST( Common_Unit_Task_Pool, TaskPool_CancelTasks )
{
    uint32_t count, maxJobs;
    IotTaskPool_t taskPool;
    const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY };
    uint32_t canceled = 0;
    uint32_t scheduled = 0;

    JobUserContext_t userContext = { 0 };

    /* In static memory mode, only the recyclable job limit may be allocated. */
    #if IOT_STATIC_MEMORY_ONLY == 1
        maxJobs = IOT_TASKPOOL_JOBS_RECYCLE_LIMIT;
        IotTaskPoolJob_t jobs[ IOT_TASKPOOL_JOBS_RECYCLE_LIMIT ] = { 0 };
    #else
        maxJobs = _TASKPOOL_TEST_ITERATIONS;
        IotTaskPoolJob_t jobs[ _TASKPOOL_TEST_ITERATIONS ] = { 0 };
    #endif

    /* Initialize user context. */
    TEST_ASSERT( IotMutex_Create( &userContext.lock, false ) );

    IotTaskPool_Create( &tpInfo, &taskPool );

    /* Create and schedule loop. */
    for( count = 0; count < maxJobs; ++count )
    {
        IotTaskPoolError_t errorSchedule;

        IotTaskPoolError_t errorCreate = IotTaskPool_CreateJob( &ExecutionWithoutDestroyCb, &userContext, &jobs[ count ] );

        switch( errorCreate )
        {
            case IOT_TASKPOOL_SUCCESS:
                break;

            case IOT_TASKPOOL_NO_MEMORY: /* OK. */
                continue;

            case IOT_TASKPOOL_BAD_PARAMETER:
                TEST_ASSERT( false );
                break;

            default:
                TEST_ASSERT( false );
        }

        errorSchedule = IotTaskPool_ScheduleDeferred( &taskPool, &jobs[ count ], 10 + ( rand() % 20 ) );

        switch( errorSchedule )
        {
            case IOT_TASKPOOL_SUCCESS:
                ++scheduled;
                break;

            case IOT_TASKPOOL_BAD_PARAMETER:
            case IOT_TASKPOOL_ILLEGAL_OPERATION:
            case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                TEST_ASSERT( false );
                break;

            default:
                TEST_ASSERT( false );
        }
    }

    /* Cancellation loop. */
    for( count = 0; count < maxJobs; ++count )
    {
        IotTaskPoolError_t error;
        IotTaskPoolJobStatus_t statusAtCancellation = IOT_TASKPOOL_STATUS_READY;
        IotTaskPoolJobStatus_t statusAfterCancellation = IOT_TASKPOOL_STATUS_READY;

        error = IotTaskPool_TryCancel( &taskPool, &jobs[ count ], &statusAtCancellation );

        switch( error )
        {
            case IOT_TASKPOOL_SUCCESS:
                canceled++;

                TEST_ASSERT(
                    ( statusAtCancellation == IOT_TASKPOOL_STATUS_READY ) ||
                    ( statusAtCancellation == IOT_TASKPOOL_STATUS_DEFERRED ) ||
                    ( statusAtCancellation == IOT_TASKPOOL_STATUS_SCHEDULED ) ||
                    ( statusAtCancellation == IOT_TASKPOOL_STATUS_CANCELED )
                    );

                TEST_ASSERT( IotTaskPool_GetStatus( &taskPool, &jobs[ count ], &statusAfterCancellation ) == IOT_TASKPOOL_SUCCESS );
                TEST_ASSERT( statusAfterCancellation == IOT_TASKPOOL_STATUS_CANCELED );
                break;

            case IOT_TASKPOOL_CANCEL_FAILED:
                TEST_ASSERT( ( statusAtCancellation == IOT_TASKPOOL_STATUS_EXECUTING ) );
                TEST_ASSERT( IotTaskPool_GetStatus( &taskPool, &jobs[ count ], &statusAfterCancellation ) == IOT_TASKPOOL_SUCCESS );
                TEST_ASSERT( ( statusAfterCancellation == IOT_TASKPOOL_STATUS_EXECUTING ) );
                break;

            case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
                /* This must be a test issue. */
                TEST_ASSERT( false );
                break;

            default:
                TEST_ASSERT( false );
                break;
        }
    }

    /* Wait until callback is executed. */
    while( ( scheduled - canceled ) != userContext.counter )
    {
        ( void ) clock_nanosleep( CLOCK_REALTIME, 0, &_TEST_DELAY_50MS.it_value, NULL );
    }

    TEST_ASSERT( ( scheduled - canceled ) == userContext.counter );

    for( count = 0; count < maxJobs; ++count )
    {
        IotTaskPool_DestroyJob( &taskPool, &jobs[ count ] );
    }

    IotTaskPool_Destroy( &taskPool );

    /* Destroy user context. */
    IotMutex_Destroy( &userContext.lock );
}

/*-----------------------------------------------------------*/
