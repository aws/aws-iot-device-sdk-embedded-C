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
 * @file aws_iot_jobs_internal.h
 * @brief Internal header of Jobs library. This header should not be included in
 * typical application code.
 */

#ifndef AWS_IOT_JOBS_INTERNAL_H_
#define AWS_IOT_JOBS_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Linear containers (lists and queues) include. */
#include "iot_linear_containers.h"

/* Jobs include. */
#include "aws_iot_jobs.h"

/* AWS IoT include. */
#include "aws_iot.h"

/**
 * @def AwsIotJobs_Assert( expression )
 * @brief Assertion macro for the Jobs library.
 *
 * Set @ref AWS_IOT_JOBS_ENABLE_ASSERTS to `1` to enable assertions in the Jobs
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if AWS_IOT_JOBS_ENABLE_ASSERTS == 1
    #ifndef AwsIotJobs_Assert
        #include <assert.h>
        #define AwsIotJobs_Assert( expression )    assert( expression )
    #endif
#else
    #define AwsIotJobs_Assert( expression )
#endif

/* Configure logs for Jobs functions. */
#ifdef AWS_IOT_LOG_LEVEL_JOBS
    #define LIBRARY_LOG_LEVEL        AWS_IOT_LOG_LEVEL_JOBS
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "Jobs" )
#include "iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "private/iot_static_memory.h"

/**
 * @brief Allocate a #_jobsOperation_t. This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    void * AwsIotJobs_MallocOperation( size_t size );

/**
 * @brief Free a #_jobsOperation_t. This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    void AwsIotJobs_FreeOperation( void * ptr );

/**
 * @brief Allocate a buffer for a short string, used for topic names or client
 * tokens. This function should have the same signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotJobs_MallocString    Iot_MallocMessageBuffer

/**
 * @brief Free a string. This function should have the same signature as
 * [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotJobs_FreeString      Iot_FreeMessageBuffer

/**
 * @brief Allocate a #_jobsSubscription_t. This function should have the
 * same signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    void * AwsIotJobs_MallocSubscription( size_t size );

/**
 * @brief Free a #_jobsSubscription_t. This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    void AwsIotJobs_FreeSubscription( void * ptr );
#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #include <stdlib.h>

    #ifndef AwsIotJobs_MallocOperation
        #define AwsIotJobs_MallocOperation    malloc
    #endif

    #ifndef AwsIotJobs_FreeOperation
        #define AwsIotJobs_FreeOperation    free
    #endif

    #ifndef AwsIotJobs_MallocString
        #define AwsIotJobs_MallocString    malloc
    #endif

    #ifndef AwsIotJobs_FreeString
        #define AwsIotJobs_FreeString    free
    #endif

    #ifndef AwsIotJobs_MallocSubscription
        #define AwsIotJobs_MallocSubscription    malloc
    #endif

    #ifndef AwsIotJobs_FreeSubscription
        #define AwsIotJobs_FreeSubscription    free
    #endif
#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS
    #define AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS    ( 5000 )
#endif
/** @endcond */

/*------------------------ Jobs internal data types -------------------------*/

/**
 * @brief Represents a Jobs subscriptions object.
 *
 * These structures are stored in a list.
 */
typedef struct _jobsSubscription
{
    IotLink_t link;         /**< @brief List link member. */

    size_t thingNameLength; /**< @brief Length of Thing Name. */
    char pThingName[];      /**< @brief Thing Name associated with this subscriptions object. */
} _jobsSubscription_t;

/**
 * @brief Internal structure representing a single Jobs operation.
 *
 * A list of these structures keeps track of all in-progress Jobs operations.
 */
typedef struct _jobsOperation
{
    IotLink_t link; /**< @brief List link member. */
} _jobsOperation_t;

/* Declarations of variables for internal Jobs files. */
extern uint32_t _AwsIotJobsMqttTimeoutMs;
extern IotListDouble_t _AwsIotJobsPendingOperations;
extern IotListDouble_t _AwsIotJobsSubscriptions;
extern IotMutex_t _AwsIotJobsPendingOperationsMutex;
extern IotMutex_t _AwsIotJobsSubscriptionsMutex;

/*------------------------ Jobs operation functions -------------------------*/

/**
 * @brief Free resources used to record a Jobs operation. This is called when
 * the operation completes.
 *
 * @param[in] pData The operation which completed. This parameter is of type
 * `void*` to match the signature of [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
void _AwsIotJobs_DestroyOperation( void * pData );

/*----------------------- Jobs subscription functions -----------------------*/

/**
 * @brief Free resources used for a Jobs subscription object.
 *
 * @param[in] pData The subscription object to destroy. This parameter is of type
 * `void*` to match the signature of [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
void _AwsIotJobs_DestroySubscription( void * pData );

#endif /* ifndef AWS_IOT_JOBS_INTERNAL_H_ */
