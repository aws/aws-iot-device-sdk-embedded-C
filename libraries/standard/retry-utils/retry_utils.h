/*
 * AWS IoT Device SDK for Embedded C V202011.00
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
 * @brief Declaration of the exponential backoff with jitter retry utility functions
 * and constants. This represents the "Full Jitter" backoff strategy explained in the
 * following document.
 * https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/
 *
 */

#ifndef RETRY_UTILS_H_
#define RETRY_UTILS_H_

/* Standard include. */
#include <stdint.h>

/**
 * @page retryutils_page Retry Utilities
 * @brief An abstraction of utilities for retrying with exponential back off and
 * jitter.
 *
 * @section retryutils_overview Overview
 * The retry utilities are a set of APIs that aid in retrying with exponential
 * backoff and jitter. Exponential backoff with jitter is strongly recommended
 * for retrying failed actions over the network with servers. Please see
 * https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/ for
 * more information about the benefits with AWS.
 *
 * Exponential backoff with jitter is typically used when retrying a failed
 * connection to the server. In an environment with poor connectivity, a client
 * can get disconnected at any time. A backoff strategy helps the client to
 * conserve battery by not repeatedly attempting reconnections when they are
 * unlikely to succeed.
 *
 * Before retrying the failed communication to the server, there is a delay period.
 * In this delay period, the task that is retrying must sleep for some random amount
 * of seconds between 0 and the lesser of the backoff window (related to the retry attempt)
 * and a predefined maximum delay value. The backoff window is doubled with each retry
 * attempt until the maximum delay value is reached.<br>
 *
 * > sleep_seconds = random_between( 0, min( 2<sup>attempts_count</sup> * base_seconds, maximum_seconds ) )
 *
 * @section retryutils_implementation Implementing Retry Utils
 *
 * The functions that must be implemented are:<br>
 * - @ref RetryUtils_ParamsReset
 * - @ref RetryUtils_BackoffAndSleep
 *
 * The functions are used as shown in the diagram below. This is the exponential
 * backoff with jitter loop:
 *
 * @image html retry_utils_flow.png width=60%
 *
 * The following steps give guidance on implementing the Retry Utils. An example
 * implementation of the Retry Utils for a POSIX platform can be found in file
 * @ref retry_utils.c.
 *
 * -# Implementing @ref RetryUtils_ParamsReset
 * @snippet this define_retryutils_paramsreset
 *<br>
 * This function initializes @ref RetryUtilsParams_t. It is expected to set
 * @ref RetryUtilsParams_t.attemptsDone to zero. It is also expected to set
 * @ref RetryUtilsParams_t.nextJitterMax to @ref INITIAL_RETRY_BACKOFF_SECONDS
 * plus some random amount of seconds, jitter. This jitter is a random number
 * between 0 and @ref MAX_JITTER_VALUE_SECONDS. This function must be called
 * before entering the exponential backoff with jitter loop using
 * @ref RetryUtils_BackoffAndSleep.<br><br>
 * Please follow the example below to implement your own @ref RetryUtils_ParamsReset.
 * The lines with FIXME comments should be updated.
 * @code{c}
 * void RetryUtils_ParamsReset( RetryUtilsParams_t * pRetryParams )
 * {
 *     uint32_t jitter = 0;
 *
 *     // Reset attempts done to zero so that the next retry cycle can start.
 *     pRetryParams->attemptsDone = 0;
 *
 *     // Seed pseudo random number generator with the current time. FIXME: Your
 *     // system may have another method to retrieve the current time to seed the
 *     // pseudo random number generator.
 *     srand( time( NULL ) );
 *
 *     // Calculate jitter value using picking a random number.
 *     jitter = ( rand() % MAX_JITTER_VALUE_SECONDS );
 *
 *     // Reset the backoff value to the initial time out value plus jitter.
 *     pRetryParams->nextJitterMax = INITIAL_RETRY_BACKOFF_SECONDS + jitter;
 * }
 * @endcode<br>
 *
 * -# Implementing @ref RetryUtils_BackoffAndSleep
 * @snippet this define_retryutils_backoffandsleep
 * <br>
 * When this function is invoked, the calling task is expected to sleep a random
 * number of seconds between 0 and @ref RetryUtilsParams_t.nextJitterMax. After
 * sleeping this function must double @ref RetryUtilsParams_t.nextJitterMax, but
 * not exceeding @ref MAX_RETRY_BACKOFF_SECONDS. When @ref MAX_RETRY_ATTEMPTS are
 * reached, this function should return @ref RetryUtilsRetriesExhausted, unless
 * @ref MAX_RETRY_ATTEMPTS is set to zero.
 * When @ref RetryUtilsRetriesExhausted is returned, the calling application can
 * stop trying with a failure, or it can call @ref RetryUtils_ParamsReset again,
 * and restart the exponential back off with jitter loop.<br><br>
 * Please follow the example below to implement your own @ref RetryUtils_BackoffAndSleep.
 * The lines with FIXME comments should be updated.
 * @code{c}
 * RetryUtilsStatus_t RetryUtils_BackoffAndSleep( RetryUtilsParams_t * pRetryParams )
 * {
 *     RetryUtilsStatus_t status = RetryUtilsRetriesExhausted;
 *     // The quiet period delay in seconds.
 *     int backOffDelay = 0;
 *
 *     // If MAX_RETRY_ATTEMPTS is set to 0, try forever.
 *     if( ( pRetryParams->attemptsDone < MAX_RETRY_ATTEMPTS ) ||
 *         ( 0 == MAX_RETRY_ATTEMPTS ) )
 *     {
 *         // Choose a random value for back-off time between 0 and the max jitter value.
 *         backOffDelay = rand() % pRetryParams->nextJitterMax;
 *
 *         //  Wait for backoff time to expire for the next retry.
 *         ( void ) myThreadSleepFunction( backOffDelay ); // FIXME: Replace with your system's thread sleep function.
 *
 *         // Increment backoff counts.
 *         pRetryParams->attemptsDone++;
 *
 *         // Double the max jitter value for the next retry attempt, only
 *         // if the new value will be less than the max backoff time value.
 *         if( pRetryParams->nextJitterMax < ( MAX_RETRY_BACKOFF_SECONDS / 2U ) )
 *         {
 *             pRetryParams->nextJitterMax += pRetryParams->nextJitterMax;
 *         }
 *         else
 *         {
 *             pRetryParams->nextJitterMax = MAX_RETRY_BACKOFF_SECONDS;
 *         }
 *
 *         status = RetryUtilsSuccess;
 *     }
 *     else
 *     {
 *         // When max retry attempts are exhausted, let application know by
 *         // returning RetryUtilsRetriesExhausted. Application may choose to
 *         // restart the retry process after calling RetryUtils_ParamsReset().
 *         status = RetryUtilsRetriesExhausted;
 *         RetryUtils_ParamsReset( pRetryParams );
 *     }
 *
 *     return status;
 * }
 * @endcode
 */

/**
 * @brief Constant to represent unlimited number of retry attempts.
 */
#define RETRY_FOREVER    0

/**
 * @brief Interface for a random number generator.
 * The user should supply the platform-specific random number number to the
 * library through the @ref RetryUtils_InitializeParams API function.
 *
 * @note It is recommended that a true random number generator is supplied
 * to the library. The random number generator should be seeded with an entropy
 * source in the system.
 *
 * @return The random number if successful; otherwise -1 to indicate failure.
 */
typedef int32_t ( * RetryUtils_RNG_t )();

/**
 * @brief Status for @ref RetryUtils_GetNextBackOff.
 */
typedef enum RetryUtilsStatus
{
    RetryUtilsSuccess = 0,     /**< @brief The function successfully calculated the next back-off value. */
    RetryUtilsRngFailure = 1,  /**< @brief The function encountered failure in generating random number. */
    RetryUtilsRetriesExhausted /**< @brief The function exhausted all retry attempts. */
} RetryUtilsStatus_t;


/**
 * @brief Represents parameters required for calculating the back-off delay for the
 * next retry attempt.
 */
typedef struct RetryUtilsContext
{
    /**
     * @brief The maximum backoff delay (in milliseconds) between consecutive retry attempts.
     */
    uint16_t maxBackOffDelay;

    /**
     * @brief The total number of retry attempts completed.
     * This value is incremented on every call to #RetryUtils_GetNextBackOff API.
     */
    uint32_t attemptsDone;

    /**
     * @brief The maximum backoff value (in milliseconds) for the next retry attempt.
     */
    uint16_t nextJitterMax;

    /**
     * @brief The maximum number of retry attempts.
     */
    uint32_t maxRetryAttempts;

    /**
     * @brief The random number generator function used for calculating the
     * backoff value for the next retry attempt.
     */
    RetryUtils_RNG_t pRng;
} RetryUtilsContext_t;

/**
 * @brief Initializes the context for using retry utils. The parameters
 * are required for calculating the next retry backoff delay.
 * This function must be called by the application before the first new retry attempt.
 *
 * @param[out] pRetryParams The context to initialize with parameters required
 * for the next backoff delay calculation function.
 * @param[in] maxBackOff The maximum backoff delay (in milliseconds) between
 * consecutive retry attempts.
 * @param[in] backOffBase The base value (in milliseconds) of backoff delay to
 * use in the exponential backoff and jitter model.
 * @param[in] maxAttempts The maximum number of retry attempts. Set the value to
 * #RETRY_FOREVER to retry for ever.
 * @param[in] pRng The platform-specific function to use for random number generation.
 * The random number generator should be seeded before calling this function.
 */
/* @[define_retryutils_initializeparams] */
void RetryUtils_InitializeParams( RetryUtilsContext_t * pContext,
                                  uint16_t backOffBase,
                                  uint16_t maxBackOff,
                                  uint32_t maxAttempts,
                                  RetryUtils_RNG_t pRng );
/* @[define_retryutils_initializeparams] */

/**
 * @brief Simple exponential backoff and jitter function that provides the
 * delay value for the next retry attempt.
 * After a failure of an operation that needs to be retried, the application
 * should use this function to obtain the backoff delay value for the next retry,
 * and then wait for the backoff value before retrying the operation.
 *
 * @param[in, out] pRetryContext Structure containing parameters for the next backoff
 * value calculation.
 * @param[out] pNextBackOff This will be populated with the backoff value (in milliseconds)
 * for the next retry attempt. The value does not exceed the maximum backoff delay
 * configured in the context.
 *
 * @return #RetryUtilsSuccess after a successful sleep, #RetryUtilsRngFailure for a failure
 * in random number generation, #RetryUtilsRetriesExhausted when all attempts are exhausted.
 */
/* @[define_retryutils_getnextbackoff] */
RetryUtilsStatus_t RetryUtils_GetNextBackOff( RetryUtilsContext_t * pRetryContext,
                                              uint16_t * pNextBackOff );
/* @[define_retryutils_getnextbackoff] */

#endif /* ifndef RETRY_UTILS_H_ */
