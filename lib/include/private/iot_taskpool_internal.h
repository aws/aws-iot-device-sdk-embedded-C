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
 * @file iot_taskpool_internal.h
 * @brief Internal header of task pool library. This header should not be included in
 * typical application code.
 */

#ifndef _IOT_TASKPOOL_INTERNAL_H_
#define _IOT_TASKPOOL_INTERNAL_H_

/* Task pool include. */
#include "iot_taskpool.h"

/**
 * @def AwsIotTaskPool_Assert( expression )
 * @brief Assertion macro for the Task Pool library.
 *
 * Set @ref AWS_IOT_TASKPOOL_ENABLE_ASSERTS to `1` to enable assertions in the Task Pool
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if AWS_IOT_TASKPOOL_ENABLE_ASSERTS == 1
    #ifndef AwsIotTaskPool_Assert
        #include <assert.h>
        #define AwsIotTaskPool_Assert( expression )    assert( expression )
    #endif
#else
    #define AwsIotTaskPool_Assert( expression )
#endif

/* Configure logs for TASKPOOL functions. */
#ifdef AWS_IOT_LOG_LEVEL_TASKPOOL
    #define _LIBRARY_LOG_LEVEL        AWS_IOT_LOG_LEVEL_TASKPOOL
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define _LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define _LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define _LIBRARY_LOG_NAME    ( "TASKPOOL" )
#include "iot_logging_setup.h"

/**
 * @brief Overridable allocator and deallocator: provide default values for undefined memory
 * allocation functions based on the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "private/iot_static_memory.h"

/**
 * @brief Overridable allocator.
 */
    #ifndef IotTaskPool_MallocJob
        #define IotTaskPool_MallocJob    Iot_MallocTaskPoolJob
    #endif

    #ifndef IotTaskPool_MallocTimerEvent
        #define IotTaskPool_MallocTimerEvent    Iot_MallocTaskPoolTimerEvent
    #endif

/**
 * @brief Overridable deallocator.
 */
    #ifndef IotTaskPool_FreeJob
        #define IotTaskPool_FreeJob    Iot_FreeTaskPoolJob
    #endif

    #ifndef IotTaskPool_FreeTimerEvent
        #define IotTaskPool_FreeTimerEvent    Iot_FreeTaskPoolTimerEvent
    #endif

#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #include <stdlib.h>

/**
 * @brief Overridable allocator.
 */
    #ifndef IotTaskPool_MallocJob
        #define IotTaskPool_MallocJob    malloc
    #endif

    #ifndef IotTaskPool_MallocTimerEvent
        #define IotTaskPool_MallocTimerEvent    malloc
    #endif

/**
 * @brief Overridable deallocator.
 */
    #ifndef IotTaskPool_FreeJob
        #define IotTaskPool_FreeJob    free
    #endif

    #ifndef IotTaskPool_FreeTimerEvent
        #define IotTaskPool_FreeTimerEvent    free
    #endif

#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef IOT_TASKPOOL_JOBS_RECYCLE_LIMIT
    #define IOT_TASKPOOL_JOBS_RECYCLE_LIMIT    ( 32 )
#endif
#ifndef AWS_IOT_TASKPOOL_THREADS_STACK_SIZE
    #define AWS_IOT_TASKPOOL_THREADS_STACK_SIZE    ( IOT_THREAD_DEFAULT_STACK_SIZE )
#endif
#ifndef AWS_IOT_TASKPOOL_THREADS_PRIORITY
    #define AWS_IOT_TASKPOOL_THREADS_PRIORITY      ( IOT_THREAD_DEFAULT_PRIORITY )
#endif
/** @endcond */

/* ---------------------------------------------------------------------------------------------- */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * A few macros to manage task pool status.
 */
#define AWS_IOT_TASKPOOL_STATUS_MASK         0x0F                 /* Lower 4 bits reserved for status (AwsIotTaskPoolJobStatus_t). */
#define AWS_IOT_TASKPOOL_FLAGS_MASK          0xF0                 /* Upper 4 bits reserved for flags. */
#define AWS_IOT_TASK_POOL_INTERNAL_STATIC    0x80                 /* Flag to mark a job as user-allocated. */
/** @endcond */

/**
 * @brief Represents an operation that is subject to a timer.
 *
 * These events are queued per MQTT connection. They are sorted by their
 * expiration time.
 */
typedef struct _taskPoolTimerEvent
{
    IotLink_t link;             /**< @brief List link member. */
    uint64_t expirationTime;    /**< @brief When this event should be processed. */
    AwsIotTaskPoolJob_t * pJob; /**< @brief The task pool job associated with this event. */
} _taskPoolTimerEvent_t;

#endif /* ifndef _IOT_TASKPOOL_INTERNAL_H_ */
