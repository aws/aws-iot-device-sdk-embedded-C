/*
 * AWS IoT Device SDK for Embedded C 202108.00
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

/* Standard includes. */
#include <assert.h>
#include <time.h>
#include <stdlib.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Demo utils header. */
#include "http_demo_utils.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/*Include clock header for millisecond sleep function. */
#include "clock.h"

/*-----------------------------------------------------------*/

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct.
 * Because these utilities are shared by both plaintext and TLS demos,
 * we must define pParams as void *. */
struct NetworkContext
{
    void * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber();

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/

int32_t connectToServerWithBackoffRetries( TransportConnect_t connectFunction,
                                           NetworkContext_t * pNetworkContext )
{
    int32_t returnStatus = EXIT_FAILURE;
    /* Status returned by the retry utilities. */
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    /* Struct containing the next backoff time. */
    BackoffAlgorithmContext_t reconnectParams;
    uint16_t nextRetryBackOff = 0U;
    struct timespec tp;

    assert( connectFunction != NULL );

    /* Seed pseudo random number generator used in the demo for
     * backoff period calculation when retrying failed network operations
     * with broker. */

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );
    /* Seed pseudo random number generator with nanoseconds. */
    srand( tp.tv_nsec );

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &reconnectParams,
                                       CONNECTION_RETRY_BACKOFF_BASE_MS,
                                       CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       CONNECTION_RETRY_MAX_ATTEMPTS );

    /* Attempt to connect to HTTP server. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached. */
    do
    {
        returnStatus = connectFunction( pNetworkContext );

        if( returnStatus != EXIT_SUCCESS )
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &reconnectParams, generateRandomNumber(), &nextRetryBackOff );

            if( backoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the HTTP server failed. Retrying "
                           "connection after %hu ms backoff.",
                           ( unsigned short ) nextRetryBackOff ) );
                Clock_SleepMs( nextRetryBackOff );
            }
            else
            {
                LogError( ( "Connection to the HTTP server failed, all attempts exhausted." ) );
            }
        }
    } while( ( returnStatus == EXIT_FAILURE ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Connection to the server failed, all attempts exhausted." ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/
