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
 * @file retry_utils.h
 * @brief Declaration of the exponential backoff retry logic utility functions
 * and constants.
 */

#ifndef RETRY_UTILS_H_
#define RETRY_UTILS_H_

/* Standard include. */
#include <stdint.h>

/**
 * @page retryutils_page Retry Utilities
 * @brief An abstraction of utilites for retrying with exponential back off and 
 * jitter
 * 
 * @section retryutils_overview Overview
 * The retry utilites are a set of APIs aiding in retrying with exponential 
 * backoff and added jitter. These utilities are implemented using your system's
 * clock and threading interface. These utilites are defined in 
 * @ref retry_utils.h Exponential backoff with added jitter is strongly 
 * reccommended for retrying failed actions over the network with servers. 
 * Please see 
 * https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/ for 
 * more information about the benefits with AWS.
 * 
 * Exponential backoff and added jitter is typically used when retrying a failed
 * connection to the server. In an environment with poor connectivity, a client
 * can get disconnected at any time. A backoff strategy helps the client to
 * conserve battery by not attempting reconnections over and over when it is
 * unlikely to succeed.
 *
 * Before retrying the action to the server there is quiet period. In this quiet
 * period, the task that is retrying must sleep for some random amount of time
 * between a base and maximum number of seconds. The base seconds is defined in
 * this API as INITIAL_RETRY_BACKOFF_SECONDS.
 * 
 * @code
 * sleep = random( INITIAL_RETRY_BACKOFF_SECONDS, maximum_seconds )
 * @endcode
 * 
 * The *maximum_seconds* starts at the INITIAL_RETRY_BACKOFF_SECONDS with some
 * added jitter. The jitter added is some random number between 0 and
 * MAX_JITTER_VALUE_SECONDS. The *maximum_seconds* doubles with each retry until
 * MAX_RETRY_BACKOFF_SECONDS is reached.
 * 
 * The quiet period is repeated 
 * 
 *
 * The functions that must be implemented are:<br>
 * - @ref RetryUtils_ParamsReset
 * - @ref RetryUtils_BackoffAndSleep
 * 
 * @section retryutils_paramsreset_implementation Implementing RetryUtils_ParamsReset
 * 
 * 
 * 
 * @section retryutils_backoffandsleep_implementation Implementing RetryUtils_BackoffAndSleep

 */

/**
 * @brief Max number of retry attempts. Set this value to 0 if the client must
 * retry forever.
 */
#define MAX_RETRY_ATTEMPTS               4U

/**
 * @brief Initial fixed backoff value in seconds between two successive
 * retries. A random jitter value is added to every backoff value.
 */
#define INITIAL_RETRY_BACKOFF_SECONDS    1U

/**
 * @brief Max backoff value in seconds.
 */
#define MAX_RETRY_BACKOFF_SECONDS        128U

/**
 * @brief Max jitter value in seconds.
 */
#define MAX_JITTER_VALUE_SECONDS         5U

/**
 * @brief Status for @ref RetryUtils_BackoffAndSleep.
 */
typedef enum RetryUtilsStatus
{
    RetryUtilsSuccess = 0,      /**< @brief The function returned successfully after sleeping. */
    RetryUtilsRetriesExhausted  /**< @brief The function exhausted all retry attempts. */
} RetryUtilsStatus_t;

/**
 * @brief Represents parameters required for retry logic.
 */
typedef struct RetryUtilsParams
{
    /**
     * @brief The cumulative count of backoff delay cycles completed
     * for retries.
     */
    uint32_t attemptsDone;

    /**
     * @brief The max jitter value for backoff time in retry attempt.
     */
    uint32_t nextJitterMax;
} RetryUtilsParams_t;


/**
 * @brief Resets the retry timeout value and number of attempts.
 * This function must be called by the application before a new retry attempt.
 *
 * @param[in, out] pRetryParams Structure containing attempts done and timeout
 * value.
 */
void RetryUtils_ParamsReset( RetryUtilsParams_t * pRetryParams );

/**
 * @brief Simple platform specific exponential backoff function. The application
 * must use this function between retry failures to add exponential delay.
 * This function will block the calling task for the current timeout value.
 *
 * @param[in, out] pRetryParams Structure containing retry parameters.
 *
 * @return #RetryUtilsSuccess after a successful sleep, #RetryUtilsRetriesExhausted
 * when all attempts are exhausted.
 */
RetryUtilsStatus_t RetryUtils_BackoffAndSleep( RetryUtilsParams_t * pRetryParams );

#endif /* ifndef RETRY_UTILS_H_ */
