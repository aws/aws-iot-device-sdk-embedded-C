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

/**
 * @brief The number of currently available Jobs operations.
 *
 * The 4 Jobs operations are GET PENDING, START NEXT, DESCRIBE, and UPDATE.
 */
#define JOBS_OPERATION_COUNT                          ( 4 )

/**
 * @brief The number of currently available Jobs callbacks.
 *
 * The 2 Jobs callbacks are `jobs/notify` (AKA "Notify Pending") and
 * `/jobs/notify-next` (AKA "Notify Next").
 */
#define JOBS_CALLBACK_COUNT                           ( 2 )

/**
 * @brief The string representing a Jobs GET PENDING operation in a Jobs MQTT topic.
 */
#define JOBS_GET_PENDING_OPERATION_STRING             "/jobs/get"

/**
 * @brief The length of #JOBS_GET_PENDING_OPERATION_STRING.
 */
#define JOBS_GET_PENDING_OPERATION_STRING_LENGTH      ( ( uint16_t ) ( sizeof( JOBS_GET_PENDING_OPERATION_STRING ) - 1 ) )

/**
 * @brief The string representing a Jobs START NEXT operation in a Jobs MQTT topic.
 */
#define JOBS_START_NEXT_OPERATION_STRING              "/jobs/start-next"

/**
 * @brief The length of #JOBS_START_NEXT_OPERATION_STRING.
 */
#define JOBS_START_NEXT_OPERATION_STRING_LENGTH       ( ( uint16_t ) ( sizeof( JOBS_START_NEXT_OPERATION_STRING ) - 1 ) )

/**
 * @brief The string representing a Jobs DESCRIBE operation in a Jobs MQTT topic.
 *
 * The %s is a placeholder for a Job ID.
 */
#define JOBS_DESCRIBE_OPERATION_STRING                "/jobs/%s/get"

/**
 * @brief The length of #JOBS_DESCRIBE_OPERATION_STRING.
 *
 * This length excludes the length of the placeholder %s.
 */
#define JOBS_DESCRIBE_OPERATION_STRING_LENGTH         ( ( uint16_t ) ( sizeof( JOBS_DESCRIBE_OPERATION_STRING ) - 3 ) )

/**
 * @brief The string representing a Jobs UPDATE operation in a Jobs MQTT topic.
 *
 * The %s is a placeholder for a Job ID.
 */
#define JOBS_UPDATE_OPERATION_STRING                  "/jobs/%s/update"

/**
 * @brief The length of #JOBS_UPDATE_OPERATION_STRING.
 *
 * This length excludes the length of the placeholder %s.
 */
#define JOBS_UPDATE_OPERATION_STRING_LENGTH           ( ( uint16_t ) ( sizeof( JOBS_UPDATE_OPERATION_STRING ) - 3 ) )

/**
 * @brief The string representing the Jobs MQTT topic for receiving notifications
 * of pending Jobs.
 */
#define JOBS_NOTIFY_PENDING_CALLBACK_STRING           "/jobs/notify"

/**
 * @brief The length of #JOBS_NOTIFY_PENDING_CALLBACK_STRING.
 */
#define JOBS_NOTIFY_PENDING_CALLBACK_STRING_LENGTH    ( ( uint16_t ) ( sizeof( JOBS_NOTIFY_PENDING_CALLBACK_STRING ) - 1 ) )

/**
 * @brief The string representing the Jobs MQTT topic for receiving notifications
 * of the next pending Job.
 */
#define JOBS_NOTIFY_NEXT_CALLBACK_STRING              "/jobs/notify-next"

/**
 * @brief The length of #JOBS_NOTIFY_NEXT_CALLBACK_STRING.
 */
#define JOBS_NOTIFY_NEXT_CALLBACK_STRING_LENGTH       ( ( uint16_t ) ( sizeof( JOBS_NOTIFY_NEXT_CALLBACK_STRING ) - 1 ) )

/**
 * @brief The maximum length of a Job ID, per AWS IoT Service Limits.
 *
 * See https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html#job-limits
 */
#define JOBS_MAX_ID_LENGTH                            ( 64 )

/**
 * @brief The length of the longest Jobs topic suffix.
 *
 * This is the length of the longest Job ID plus the length of the "UPDATE"
 * operation suffix.
 */
#define JOBS_LONGEST_SUFFIX_LENGTH                    ( JOBS_MAX_ID_LENGTH + JOBS_UPDATE_OPERATION_STRING_LENGTH )

/*------------------------ Jobs internal data types -------------------------*/

/**
 * @brief Enumerations representing each of the Jobs library's API functions.
 */
typedef enum _jobsOperationType
{
    /* Jobs operations. */
    JOBS_GET_PENDING = 0, /**< @ref jobs_function_getpending */
    JOBS_START_NEXT = 1,  /**< @ref jobs_function_startnext */
    JOBS_DESCRIBE = 2,    /**< @ref jobs_function_describe */
    JOBS_UPDATE = 3,      /**< @ref jobs_function_update */

    /* Jobs callbacks. */
    SET_NOTIFY_PENDING_CALLBACK = 4, /**< @ref jobs_function_setnotifypendingcallback */
    SET_NOTIFY_NEXT_CALLBACK = 5     /**< @ref jobs_function_setnotifynextcallback */
} _jobsOperationType_t;

/**
 * @brief Represents a Jobs subscriptions object.
 *
 * These structures are stored in a list.
 */
typedef struct _jobsSubscription
{
    IotLink_t link;                                           /**< @brief List link member. */

    int32_t references[ JOBS_OPERATION_COUNT ];               /**< @brief Reference counter for Jobs operation topics. */
    AwsIotJobsCallbackInfo_t callback[ JOBS_CALLBACK_COUNT ]; /**< @brief Jobs callbacks for this Thing. */

    /**
     * @brief Buffer allocated for removing Jobs topics.
     *
     * This buffer is pre-allocated to ensure that memory is available when
     * unsubscribing.
     */
    char * pTopicBuffer;

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

    /* Basic operation information. */
    _jobsOperationType_t type;           /**< @brief Operation type. */
    uint32_t flags;                      /**< @brief Flags passed to operation API function. */
    AwsIotJobsError_t status;            /**< @brief Status of operation. */

    IotMqttConnection_t mqttConnection;  /**< @brief MQTT connection associated with this operation. */
    _jobsSubscription_t * pSubscription; /**< @brief Jobs subscriptions object associated with this operation. */

    /* Jobs request information. */
    const char * pJobsRequest; /**< @brief JSON document to send to the Jobs service. */
    size_t jobsRequestLength;  /**< @brief Length of #_jobsOperation_t.pJobsRequest. */

    const char * pClientToken; /**< @brief Client token sent with request. */
    size_t clientTokenLength;  /**< @brief Length of #_jobsOperation_t.pClientToken. */

    /* Jobs response information. */
    const char * pJobsResponse; /**< @brief Response received from the Jobs service. */
    size_t jobsResponseLength;  /**< @brief Length of #_jobsOperation_t.pJobsResponse. */

    /**
     * @brief Function to allocate memory for an incoming Jobs response.
     *
     * Only used when the flag #AWS_IOT_JOBS_FLAG_WAITABLE is set.
     */
    void * ( *mallocResponse )( size_t );

    /* How to notify of an operation's completion. */
    union
    {
        IotSemaphore_t waitSemaphore;      /**< @brief Semaphore to be used with @ref jobs_function_wait. */
        AwsIotJobsCallbackInfo_t callback; /**< @brief User-provided callback function and parameter. */
    } notify;                              /**< @brief How to notify of an operation's completion. */
} _jobsOperation_t;

/* Declarations of names printed in logs. */
#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
    extern const char * const _pAwsIotJobsOperationNames[];
#endif

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

/*--------------------------- Jobs JSON functions ---------------------------*/

/**
 * @brief Generates a Jobs JSON request document from an #AwsIotJobsRequestInfo_t
 * and an #AwsIotJobsUpdateInfo_t.
 *
 * @param[in] type The type of Jobs operation for the request.
 * @param[in] pRequestInfo Common Jobs request parameters.
 * @param[in] pUpdateInfo Jobs update parameters.
 * @param[out] pRequestJson Set to a buffer containing the request JSON.
 * @param[out] pRequestJsonLength Set to the length of the request JSON.
 *
 * @return #AWS_IOT_JOBS_SUCCESS on success; otherwise, #AWS_IOT_JOBS_NO_MEMORY.
 */
AwsIotJobsError_t _AwsIotJobs_GenerateJsonRequest( _jobsOperationType_t type,
                                                   const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                   const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                                   const char ** pRequestJson,
                                                   size_t * pRequestJsonLength );

#endif /* ifndef AWS_IOT_JOBS_INTERNAL_H_ */
