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
 * - @functionname{jobs_function_update}
 * - @functionname{jobs_function_strerror}
 * - @functionname{jobs_function_statename}
 */

/**
 * @functionpage{AwsIotJobs_Update,jobs,update}
 * @functionpage{AwsIotJobs_strerror,jobs,strerror}
 * @functionpage{AwsIotJobs_StateName,jobs,statename}
 */

/**
 * @brief Update the status of a job execution and receive an asynchronous
 * notification when the Job update completes.
 */
/* @[declare_jobs_update] */
AwsIotJobsError_t AwsIotJobs_Update( void );
/* @[declare_jobs_update] */

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
