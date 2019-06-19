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
 * @file aws_iot_jobs_types.h
 * @brief Types of the Jobs library.
 */

#ifndef AWS_IOT_JOBS_TYPES_H_
#define AWS_IOT_JOBS_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/*---------------------------- Jobs handle types ----------------------------*/

/**
 * @handles{jobs,Jobs library}
 */

/**
 * @ingroup jobs_datatypes_handles
 * @brief Opaque handle that references an in-progress Jobs operation.
 */
typedef struct _jobsOperation * AwsIotJobsOperation_t;

/*-------------------------- Jobs enumerated types --------------------------*/

/**
 * @enums{jobs,Jobs library}
 */

/**
 * @ingroup jobs_datatypes_enums
 * @brief Return codes of [Jobs functions](@ref jobs_functions).
 *
 * The function @ref jobs_function_strerror can be used to get a return code's
 * description.
 *
 * The values between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE
 * may be returned by the Jobs service upon failure of a Jobs operation. See [this page]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#jobs-mqtt-error-response)
 * for more information.
 */
typedef enum AwsIotJobsError
{
    /**
     * @brief Jobs operation completed successfully.
     */
    AWS_IOT_JOBS_SUCCESS = 0,

    /**
     * @brief Jobs operation queued, awaiting result.
     */
    AWS_IOT_JOBS_STATUS_PENDING,

    /**
     * @brief Initialization failed.
     */
    AWS_IOT_JOBS_INIT_FAILED,

    /**
     * @brief At least one parameter is invalid.
     */
    AWS_IOT_JOBS_BAD_PARAMETER,

    /**
     * @brief Jobs operation failed because of memory allocation failure.
     */
    AWS_IOT_JOBS_NO_MEMORY,

    /**
     * @brief Jobs operation failed because of failure in MQTT library.
     */
    AWS_IOT_JOBS_MQTT_ERROR,

    /**
     * @brief Response received from Jobs service not understood.
     */
    AWS_IOT_JOBS_BAD_RESPONSE,

    /**
     * @brief A blocking Jobs operation timed out.
     */
    AWS_IOT_JOBS_TIMEOUT,

    /**
     * @brief Jobs operation failed: A request was sent to an unknown topic.
     */
    AWS_IOT_JOBS_INVALID_TOPIC,

    /**
     * @brief Jobs operation failed: The contents of the request were not understood.
     *
     * Jobs requests must be UTF-8 encoded JSON documents.
     */
    AWS_IOT_JOBS_INVALID_JSON,

    /**
     * @brief Jobs operation failed: The contents of the request were invalid.
     */
    AWS_IOT_JOBS_INVALID_REQUEST,

    /**
     * @brief Jobs operation failed: An update attempted to change the job execution
     * to an invalid state.
     */
    AWS_IOT_JOBS_INVALID_STATE,

    /**
     * @brief Jobs operation failed: The specified job execution does not exist.
     */
    AWS_IOT_JOBS_NOT_FOUND,

    /**
     * @brief Jobs operation failed: The Jobs service expected a version that did
     * not match what was in the request.
     */
    AWS_IOT_JOBS_VERSION_MISMATCH,

    /**
     * @brief Jobs operation failed: The Jobs service encountered an internal error.
     */
    AWS_IOT_JOBS_INTERNAL_ERROR,

    /**
     * @brief Jobs operation failed: The request was throttled.
     */
    AWS_IOT_JOBS_THROTTLED,

    /**
     * @brief Jobs operation failed: Attempt to describe a Job in a terminal state.
     */
    AWS_IOT_JOBS_TERMINAL_STATE
} AwsIotJobsError_t;

/**
 * @ingroup jobs_datatypes_enums
 * @brief Possible states of jobs.
 *
 * The function @ref jobs_function_statename can be used to get a state's
 * description.
 *
 * See [this page]
 * (https://docs.aws.amazon.com/iot/latest/apireference/API_iot-jobs-data_JobExecutionState.html)
 * for more information on Job states.
 */
typedef enum AwsIotJobsState
{
    /**
     * @brief A Job is queued and awaiting execution.
     */
    AWS_IOT_JOB_STATE_QUEUED,

    /**
     * @brief A Job is currently executing.
     */
    AWS_IOT_JOB_STATE_IN_PROGRESS,

    /**
     * @brief A Job has failed. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_FAILED,

    /**
     * @brief A Job has succeeded. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_SUCCEEDED,

    /**
     * @brief A Job was canceled. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_CANCELED,

    /**
     * @brief A Job's timer has expired. This is a terminal state.
     *
     * Jobs are considered timed out if they remain [IN_PROGRESS]
     * (@ref AWS_IOT_JOB_STATE_IN_PROGRESS) for more than their
     * `inProgressTimeoutInMinutes` property or a [Job update](@ref jobs_function_update)
     * was not sent within [stepTimeoutInMinutes](@ref x).
     */
    AWS_IOT_JOB_STATE_TIMED_OUT,

    /**
     * @brief A Job was rejected by the device. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_REJECTED,

    /**
     * @brief A Job was removed. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_REMOVED
} AwsIotJobState_t;

#endif /* ifndef AWS_IOT_JOBS_TYPES_H_ */
