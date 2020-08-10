/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file jobs.h
 * @brief Integration for the AWS IoT jobs APIs
 *
 * https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#jobs-mqtt-api
 */

#ifndef JOBS_H_
#define JOBS_H_

#include <stddef.h>
#include <stdint.h>

#define JOBS_THINGNAME_MAX_LENGTH         128U /* per AWS IoT API Reference */
#define JOBS_JOBID_MAX_LENGTH             64U  /* per AWS IoT API Reference */

#define JOBS_API_PREFIX                   "$aws/things/"
#define JOBS_API_PREFIX_LENGTH            ( sizeof( JOBS_API_PREFIX ) - 1U )

#define JOBS_API_BRIDGE                   "/jobs/"
#define JOBS_API_BRIDGE_LENGTH            ( sizeof( JOBS_API_BRIDGE ) - 1U )

#define JOBS_API_SUCCESS                  "/accepted"
#define JOBS_API_SUCCESS_LENGTH           ( sizeof( JOBS_API_SUCCESS ) - 1U )

#define JOBS_API_FAILURE                  "/rejected"
#define JOBS_API_FAILURE_LENGTH           ( sizeof( JOBS_API_FAILURE ) - 1U )

#define JOBS_API_JOBSCHANGED              "notify"
#define JOBS_API_JOBSCHANGED_LENGTH       ( sizeof( JOBS_API_JOBSCHANGED ) - 1U )

#define JOBS_API_NEXTJOBCHANGED           "notify-next"
#define JOBS_API_NEXTJOBCHANGED_LENGTH    ( sizeof( JOBS_API_NEXTJOBCHANGED ) - 1U )

#define JOBS_API_GETPENDING               "get"
#define JOBS_API_GETPENDING_LENGTH        ( sizeof( JOBS_API_GETPENDING ) - 1U )

#define JOBS_API_STARTNEXT                "start-next"
#define JOBS_API_STARTNEXT_LENGTH         ( sizeof( JOBS_API_STARTNEXT ) - 1U )

#define JOBS_API_DESCRIBE                 "get"
#define JOBS_API_DESCRIBE_LENGTH          ( sizeof( JOBS_API_DESCRIBE ) - 1U )

#define JOBS_API_UPDATE                   "update"
#define JOBS_API_UPDATE_LENGTH            ( sizeof( JOBS_API_UPDATE ) - 1U )

#define JOBS_API_MAX_LENGTH( thingNameLength )                         \
    ( JOBS_API_PREFIX_LENGTH + ( thingNameLength ) +                   \
      JOBS_API_BRIDGE_LENGTH + JOBS_JOBID_MAX_LENGTH + sizeof( '/' ) + \
      JOBS_API_UPDATE_LENGTH + JOBS_API_SUCCESS_LENGTH + 1 )

#define JOBS_API_COMMON_LENGTH( thingNameLength ) \
    ( JOBS_API_PREFIX_LENGTH + ( thingNameLength ) + JOBS_API_BRIDGE_LENGTH )

/**
 * @brief Return codes from jobs functions.
 */
typedef enum
{
    JobsError = 0,
    JobsSuccess,
    JobsNoMatch,
    JobsBadParameter,
    JobsBufferTooSmall
} JobsStatus_t;

/**
 * @brief Topic values for subscription requests.
 */
typedef enum
{
    JobsInvalidTopic = -1,
    JobsJobsChanged,
    JobsNextJobChanged,
    JobsGetPendingSuccess,
    JobsGetPendingFailed,
    JobsStartNextSuccess,
    JobsStartNextFailed,
    JobsDescribeSuccess,
    JobsDescribeFailed,
    JobsUpdateSuccess,
    JobsUpdateFailed,
    JobsMaxTopic
} JobsTopic_t;

/**
 * @brief Populate a topic string for a subscription request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[in] api  The desired Jobs API, e.g., JobsNextJobChanged.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName parameter does not need a NULL terminator.
 */
JobsStatus_t Jobs_GetTopic( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            JobsTopic_t api,
                            size_t * outLength );

/**
 * @brief Output a topic value if a Jobs API topic string is present.
 * Optionally, output a pointer to a jobID within the topic and its
 * length.
 *
 * @param[in] topic  The topic string to check.
 * @param[in] length  The length of the topic string.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] outApi  The jobs topic API value if present, e.g., #JobsUpdateSuccess.
 * @param[out] outJobId  The beginning of the jobID in the topic string.
 * @param[out] outJobIdLength  The length of the jobID in the topic string.
 *
 * @return #JobsSuccess if a matching topic was found;
 * #JobsNoMatch if a matching topic was NOT found
 *   (parameter outApi gets #JobsInvalidTopic );
 * #JobsBadParameter if invalid parameters are passed.
 *
 * @note The topic and thingName parameters do not need a NULL terminator.
 *
 * @note Not all Jobs APIs have jobIDs within the topic string.
 * NULL and 0 are output when no jobID is present.
 * The parameters jobId and jobIdLength may be NULL to ignore jobIDs.
 */
JobsStatus_t Jobs_MatchTopic( const char * topic,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              JobsTopic_t * outApi,
                              char ** outJobId,
                              uint16_t * outJobIdLength );

/**
 * @brief Populate a topic string for a GetPendingJobExecutions request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName parameter does not need a NULL terminator.
 */
JobsStatus_t Jobs_GetPending( char * buffer,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              size_t * outLength );

/**
 * @brief Populate a topic string for a StartNextPendingJobExecution request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName parameter does not need a NULL terminator.
 */
JobsStatus_t Jobs_StartNext( char * buffer,
                             size_t length,
                             const char * thingName,
                             uint16_t thingNameLength,
                             size_t * outLength );

/**
 * @brief Populate a topic string for a DescribeJobExecution request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] jobId  The ID of the job to describe.
 * @param[out] jobIdLength  The length of the job ID.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName and jobId parameters do not need a NULL terminator.
 */
JobsStatus_t Jobs_Describe( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            const char * jobId,
                            uint16_t jobIdLength,
                            size_t * outLength );

/**
 * @brief Populate a topic string for an UpdateJobExecution request.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 * @param[out] jobId  The ID of the job to describe.
 * @param[out] jobIdLength  The length of the job ID.
 * @param[out] outLength  The length of the topic string written to the buffer.
 *
 * @return #JobsSuccess if the topic was written to the buffer;
 * #JobsBadParameter if invalid parameters are passed;
 * #JobsBufferTooSmall if the buffer cannot hold the full topic string.
 *
 * When all parameters are valid, the topic string is written to
 * the buffer up to one less than the buffer size.  The topic is
 * ended with a NUL character.
 *
 * @note The thingName and jobId parameters do not need a NULL terminator.
 */
JobsStatus_t Jobs_Update( char * buffer,
                          size_t length,
                          const char * thingName,
                          uint16_t thingNameLength,
                          const char * jobId,
                          uint16_t jobIdLength,
                          size_t * outLength );

#endif /* ifndef JOBS_H_ */
