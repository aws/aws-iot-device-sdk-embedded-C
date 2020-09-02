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

#ifndef RETRY_UTILS__H_
#define RETRY_UTILS__H_

/* Standard include. */
#include <stdint.h>

/* bool is defined in only C99+. */
#if defined( __cplusplus ) || ( ( defined( __STDC_VERSION__ ) ) && ( __STDC_VERSION__ >= 199901L ) )
    #include <stdbool.h>
#elif !defined( bool )
    #define bool     signed char
    #define false    0
    #define true     1
#endif

/* @brief Max number of retry attempts, set this value to 0 if the client
 * must retry forever */
#define MAX_RETRY_ATTEMPTS               4U

/* @brief Initial fixed backoff value in seconds between two successive
 * retries. A random jitter value is added to every backoff value  */
#define INITIAL_RETRY_BACKOFF_SECONDS    1U
/* @brief Max backoff value in seconds */
#define MAX_RETRY_BACKOFF_SECONDS        128U
/* @brief Max jitter value in seconds */
#define MAX_JITTER_VALUE_SECONDS         5U

/* @brief Represents parameters required for retry logic. */
typedef struct RetryUtilsParams
{
    /* @brief The cumulative count of backoff delay cycles completed
     * for retries. */
    uint32_t attemptsDone;

    /** @brief The max jitter value for backoff time in retry attempt. */
    uint32_t nextJitterMax;
} RetryUtilsParams_t;


/**
 * @brief Reset retry timeout value and number of attempts.
 * This function must be called by the application before a new retry attempt.
 *
 * @param[in, out] pRetryParams structure containing attempts done and timeout
 * value.
 */
void RetryUtils_ParamsReset( RetryUtilsParams_t * pRetryParams );

/**
 * @brief Simple platform specific exponential backoff function. The application
 * must use this function between retry failures to add exponential delay.
 * This function will block the calling task for the current timeout value.
 *
 * @param[in, out] pRetryParams structure containing retry parameters.
 *
 * @return true after successful sleep, false when all attempts are exhausted.
 */
bool RetryUtils_BackoffAndSleep( RetryUtilsParams_t * pRetryParams );

#endif /* ifndef RETRY_UTILS_H_ */
