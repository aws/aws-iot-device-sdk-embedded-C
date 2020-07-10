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
 * @file transport_reconnect_posix.c
 * @brief Implementation of the backoff logic when connection fails to the server fails.
 */

/* Standard includes. */
#include <unistd.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include "transport_reconnect.h"

#define JITTER_MAX_MSB_BIT_MASK    ( )

/*-----------------------------------------------------------*/

bool Transport_ReconnectBackoffAndSleep( TransportReconnectParams_t * pReconnectParams )
{
    bool status = false;

    /* If MAX_RECONNECT_ATTEMPTS is set to 0, try forever */
    if( ( pReconnectParams->attemptsDone < MAX_RECONNECT_ATTEMPTS ) ||
        ( 0 == MAX_RECONNECT_ATTEMPTS ) )
    {
        /*  Wait for backoff time to expire for the next reconnect. */
        ( void ) sleep( ( rand() % pReconnectParams->nextJitterMax ) );

        /* Increment backoff counts. */
        pReconnectParams->attemptsDone++;

        /* Double the max jitter value for the next reconnect attempt, only
        * if the new value will be less than the max backoff time value. */
        if( pReconnectParams->nextJitterMax < ( MAX_RECONNECT_BACKOFF_SECONDS / 2U ) )
        {
            pReconnectParams->nextJitterMax += pReconnectParams->nextJitterMax;
        }
        else
        {
            pReconnectParams->nextJitterMax = MAX_RECONNECT_BACKOFF_SECONDS;
        }

        status = true;
    }
    else
    {
        /* When max reconnect attempts are exhausted, let application know by returning
         * false. Application may choose to restart the connection process after calling
         * Transport_ReconnectParamsReset(). */
        status = false;
        Transport_ReconnectParamsReset( pReconnectParams );
    }

    return status;
}

/*-----------------------------------------------------------*/

void Transport_ReconnectParamsReset( TransportReconnectParams_t * pReconnectParams )
{
    uint32_t jitter = 0;
    struct timespec tp;

    /* Reset attempts done to zero so that the next connect cycle can start. */
    pReconnectParams->attemptsDone = 0;

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );

    /* Seed pseudo ramdom number generator with nano seconds. */
    srand( tp.tv_nsec );

    /* Calculate jitter value using picking a random number. */
    jitter = ( rand() % MAX_JITTER_VALUE_SECONDS );

    /* Reset the backoff value to the initial time out value plus jitter. */
    pReconnectParams->nextJitterMax = INITIAL_RECONNECT_BACKOFF_SECONDS + jitter;
}

/*-----------------------------------------------------------*/
