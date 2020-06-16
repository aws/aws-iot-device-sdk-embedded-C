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
 * @file reconnect_posix.c
 * @brief Implementation of the backoff logic when connection fails to the server fails.
 */

/* Standard includes. */
#include <unistd.h>
#include <stdlib.h>
#include <time.h>
#include "reconnect.h"

/*-----------------------------------------------------------*/

bool reconnectBackoffAndSleep( TransportReconnectParams_t * pReconnectParams )
{
    bool status = false;
   
    /* MAX_RECONNECT_ATTEMPTS is set to 0, try for ever */
    if( ( pReconnectParams->attemptsDone < MAX_RECONNECT_ATTEMPS ) ||
        ( 0 == MAX_RECONNECT_ATTEMPS ) )
    {
        /* Check if we have reached the max time out value */
        if( pReconnectParams->reconnectTimeoutSec > MAX_RECONNECT_TIMEOUT )
        {
            pReconnectParams->reconnectTimeoutSec = MAX_RECONNECT_TIMEOUT;
        }
        
        /* Continue to wait for timer to expire for the next reconnect */
        ( void ) sleep( pReconnectParams->reconnectTimeoutSec );
        pReconnectParams->reconnectTimeoutSec += pReconnectParams->reconnectTimeoutSec;
        pReconnectParams->attemptsDone++;
        status = true;
    }
    else
    {
        status = false;
        reconnectBackoffReset( pReconnectParams );
    }

    return status;
}

/*-----------------------------------------------------------*/

void reconnectBackoffReset( TransportReconnectParams_t * pReconnectParams )
{
    uint32_t jitter = 0;
    struct timespec tp;

    /* Reset attempts done to zero so that the next connect cycle can start */
    pReconnectParams->attemptsDone = 0;

    /* Get current time to seed pseudo random number generator */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );

    /* Seed pseudo ramdom number generator with nano seconds */
    srand( tp.tv_nsec );

    /* Calculate jitter value using picking a random number. */
    jitter = ( rand() % 5 );

    /* Reset the timout value to the initial time out value plus jitter */
    pReconnectParams->reconnectTimeoutSec = RECONNECT_INITIAL_TIMEOUT_SECONDS + jitter;
}

/*-----------------------------------------------------------*/
