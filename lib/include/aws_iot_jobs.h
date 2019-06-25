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
 * @file aws_iot_jobs.h
 * @brief User-facing functions of the Jobs library.
 */

#ifndef AWS_IOT_JOBS_H_
#define AWS_IOT_JOBS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Jobs types include. */
#include "types/aws_iot_jobs_types.h"

/*------------------------- Jobs library functions --------------------------*/

/**
 * @functionspage{jobs,Jobs library}
 * - @functionname{jobs_function_init}
 * - @functionname{jobs_function_cleanup}
 * - @functionname{jobs_function_getpending}
 * - @functionname{jobs_function_timedgetpending}
 * - @functionname{jobs_function_startnext}
 * - @functionname{jobs_function_timedstartnext}
 * - @functionname{jobs_function_describe}
 * - @functionname{jobs_function_timeddescribe}
 * - @functionname{jobs_function_update}
 * - @functionname{jobs_function_timedupdate}
 * - @functionname{jobs_function_wait}
 * - @functionname{jobs_function_setnotifypendingcallback}
 * - @functionname{jobs_function_setnotifynextcallback}
 * - @functionname{jobs_function_removepersistentsubscriptions}
 * - @functionname{jobs_function_strerror}
 * - @functionname{jobs_function_statename}
 */

/**
 * @functionpage{AwsIotJobs_Init,jobs,init}
 * @functionpage{AwsIotJobs_Cleanup,jobs,cleanup}
 * @functionpage{AwsIotJobs_GetPending,jobs,getpending}
 * @functionpage{AwsIotJobs_TimedGetPending,jobs,timedgetpending}
 * @functionpage{AwsIotJobs_StartNext,jobs,startnext}
 * @functionpage{AwsIotJobs_TimedStartNext,jobs,timedstartnext}
 * @functionpage{AwsIotJobs_Describe,jobs,describe}
 * @functionpage{AwsIotJobs_TimedDescribe,jobs,timeddescribe}
 * @functionpage{AwsIotJobs_Update,jobs,update}
 * @functionpage{AwsIotJobs_TimedUpdate,jobs,timedupdate}
 * @functionpage{AwsIotJobs_Wait,jobs,wait}
 * @functionpage{AwsIotJobs_SetNotifyPendingCallback,jobs,setnotifypendingcallback}
 * @functionpage{AwsIotJobs_SetNotifyNextCallback,jobs,setnotifynextcallback}
 * @functionpage{AwsIotJobs_RemovePersistentSubscriptions,jobs,removepersistentsubscriptions}
 * @functionpage{AwsIotJobs_strerror,jobs,strerror}
 * @functionpage{AwsIotJobs_StateName,jobs,statename}
 */

/**
 * @brief One-time initialization function for the Jobs library.
 *
 * This function performs internal setup of the Jobs library. <b>It must be
 * called once (and only once) before calling any other Jobs function.</b>
 * Calling this function more than once without first calling @ref
 * jobs_function_cleanup may result in a crash.
 *
 * @param[in] mqttTimeoutMs The amount of time (in milliseconds) that the Jobs
 * library will wait for MQTT operations. Optional; set this to `0` to use
 * @ref AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_INIT_FAILED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref jobs_function_cleanup
 */
/* @[declare_jobs_init] */
AwsIotJobsError_t AwsIotJobs_Init( uint32_t mqttTimeoutMs );
/* @[declare_jobs_init] */

/**
 * @brief One-time deinitialization function for the Jobs library.
 *
 * This function frees resources taken in @ref jobs_function_init and deletes
 * any [persistent subscriptions.](@ref AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS)
 * It should be called to clean up the Jobs library. After this function returns,
 * @ref jobs_function_init must be called again before calling any other Jobs
 * function.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref jobs_function_init
 */
/* @[declare_jobs_cleanup] */
void AwsIotJobs_Cleanup( void );
/* @[declare_jobs_cleanup] */

/**
 * @brief Get the list of all pending jobs for a Thing and receive an asynchronous
 * notification when the response arrives.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pGetPendingOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Jobs operation
 * completes.
 *
 * @return This function will return #AWS_IOT_JOBS_STATUS_PENDING upon successfully
 * queuing the Jobs operation.
 * @return If this function fails before queuing the Jobs operation, it will return one of:
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * @return Upon successful completion of the Jobs operation (either through an #AwsIotJobsCallbackInfo_t
 * or #AwsIotJobs_Wait), the status will be #AWS_IOT_JOBS_SUCCESS.
 * @return Should the Jobs operation fail, the status will be one of:
 * - #AWS_IOT_JOBS_NO_MEMORY (Memory could not be allocated for incoming document)
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 *
 * @see @ref jobs_function_timedgetpending for a blocking variant of this function.
 */
/* @[declare_jobs_getpending] */
AwsIotJobsError_t AwsIotJobs_GetPending( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                         uint32_t flags,
                                         const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                         AwsIotJobsOperation_t * const pGetPendingOperation );
/* @[declare_jobs_getpending] */

/**
 * @brief Get the list of all pending jobs for a Thing with a timeout for receiving
 * the response.
 */
/* @[declare_jobs_timedgetpending] */
AwsIotJobsError_t AwsIotJobs_TimedGetPending( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                              uint32_t flags,
                                              uint32_t timeout );
/* @[declare_jobs_timedgetpending] */

/**
 * @brief Start the next pending job execution for a Thing and receive an asynchronous
 * notification when the response arrives.
 */
/* @[declare_jobs_startnext] */
AwsIotJobsError_t AwsIotJobs_StartNext( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                        const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                        uint32_t flags,
                                        const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                        AwsIotJobsOperation_t * const pStartNextOperation );
/* @[declare_jobs_startnext] */

/**
 * @brief Start the next pending job execution for a Thing with a timeout for
 * receiving the response.
 */
/* @[declare_jobs_timedstartnext] */
AwsIotJobsError_t AwsIotJobs_TimedStartNext( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                             const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                             uint32_t flags,
                                             uint32_t timeout );
/* @[declare_jobs_timedstartnext] */

/**
 * @brief Get detailed information about a job execution and receive an asynchronous
 * notification when the response arrives.
 */
/* @[declare_jobs_describe] */
AwsIotJobsError_t AwsIotJobs_Describe( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                       int32_t executionNumber,
                                       bool includeJobDocument,
                                       uint32_t flags,
                                       const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                       AwsIotJobsOperation_t * const pDescribeOperation );
/* @[declare_jobs_describe] */

/**
 * @brief Get detailed information about a job execution with a timeout for receiving
 * the response.
 */
/* @[declare_jobs_timeddescribe] */
AwsIotJobsError_t AwsIotJobs_TimedDescribe( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            int32_t executionNumber,
                                            bool includeJobDocument,
                                            uint32_t flags,
                                            uint32_t timeout );
/* @[declare_jobs_timeddescribe] */

/**
 * @brief Update the status of a job execution and receive an asynchronous
 * notification when the Job update completes.
 */
/* @[declare_jobs_update] */
AwsIotJobsError_t AwsIotJobs_Update( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                     const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                     uint32_t flags,
                                     const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                     AwsIotJobsOperation_t * const pUpdateOperation );
/* @[declare_jobs_update] */

/**
 * @brief Update the status of a job execution with a timeout for receiving the
 * response.
 */
/* @[declare_jobs_timedupdate] */
AwsIotJobsError_t AwsIotJobs_TimedUpdate( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                          const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                          uint32_t flags,
                                          uint32_t timeout );
/* @[declare_jobs_timedupdate] */

/**
 * @brief Wait for a Jobs operation to complete.
 */
/* @[declare_jobs_wait] */
AwsIotJobsError_t AwsIotJobs_Wait( AwsIotJobsOperation_t operation,
                                   uint32_t timeoutMs,
                                   const char ** const pResponse,
                                   size_t * const pResponseLength );
/* @[declare_jobs_wait] */

/**
 * @brief Set a callback to be invoked when the list of pending Jobs changes.
 */
/* @[declare_jobs_setnotifypendingcallback] */
AwsIotJobsError_t AwsIotJobs_SetNotifyPendingCallback( IotMqttConnection_t mqttConnection,
                                                       const char * pThingName,
                                                       size_t thingNameLength,
                                                       uint32_t flags,
                                                       const AwsIotJobsCallbackInfo_t * pNotifyPendingCallback );
/* @[declare_jobs_setnotifypendingcallback] */

/**
 * @brief Set a callback to be invoked when the next pending Job changes.
 */
/* @[declare_jobs_setnotifynextcallback] */
AwsIotJobsError_t AwsIotJobs_SetNotifyNextCallback( IotMqttConnection_t mqttConnection,
                                                    const char * pThingName,
                                                    size_t thingNameLength,
                                                    uint32_t flags,
                                                    const AwsIotJobsCallbackInfo_t * pNotifyNextCallback );
/* @[declare_jobs_setnotifynextcallback] */

/**
 * @brief Remove persistent Jobs operation topic subscriptions.
 */
/* @[declare_jobs_removepersistentsubscriptions] */
AwsIotJobsError_t AwsIotJobs_RemovePersistentSubscriptions( IotMqttConnection_t mqttConnection,
                                                            const char * pThingName,
                                                            size_t thingNameLength,
                                                            uint32_t flags );
/* @[declare_jobs_removepersistentsubscriptions] */

/*-------------------------- Jobs helper functions --------------------------*/

/**
 * @brief Returns a string that describes an #AwsIotJobsError_t.
 *
 * Like POSIX's `strerror`, this function returns a string describing a return
 * code. In this case, the return code is a Jobs library error code, `status`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] status The status to describe.
 *
 * @return A read-only string that describes `status`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_jobs_strerror] */
const char * AwsIotJobs_strerror( AwsIotJobsError_t status );
/* @[declare_jobs_strerror] */

/**
 * @brief Returns a string that describes an #AwsIotJobState_t.
 *
 * This function returns a string describing a Job state, `state`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] state The job state to describe.
 *
 * @return A read-only string that describes `state`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_jobs_statename] */
const char * AwsIotJobs_StateName( AwsIotJobState_t state );
/* @[declare_jobs_statename] */

#endif /* ifndef AWS_IOT_JOBS_H_ */
