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
 * @file reconnect_config.h
 * @brief Declaration of the exponential backoff reconnect logic utility functions
 * and constants.
 */

#ifndef RECONNECT_H_
#define RECONNECT_H_

#include <stdint.h>

/* bools are only defined in C99+ */
#if defined( __cplusplus ) || __STDC_VERSION__ >= 199901L
    #include <stdbool.h>
#elif !defined( bool )
    #define bool     signed char
    #define false    0
    #define true     1
#endif

/* @brief Max number of connect attempts, set this value to 0 if the client
 * must try connecting to the server forever */
#define MAX_RECONNECT_ATTEMPS                4U

/* @brief Initial fixed timeout value in seconds between two successive
 * connects. A random jitter value is added to every timeout value  */
#define INITIAL_RECONNECT_TIMEOUT_SECONDS    1U
/* @brief Max timout value in seconds */
#define MAX_RECONNECT_TIMEOUT_SECONDS        128U
/* @brief Max jitter value in seconds */
#define MAX_JITTER_VALUE_SECONDS             5U


/* @brief Transport reconnect parameter */
typedef struct TransportReconnectParams
{
    uint32_t reconnectTimeoutSec;
    uint32_t attemptsDone;
} TransportReconnectParams_t;


/**
 * @brief Reset reconnection timeout value and number of attempts.
 * This function must be called by the application before a new connection
 * with the server is attempted.
 *
 * @param[in, out] reconnectParam structure containing attempts done and timeout
 * value.
 */
void Transport_ReconnectParamsReset( TransportReconnectParams_t * reconnectParams );

/**
 * @brief Simple platfrom specific exponential backoff function. The application
 * must use this function between connection failures to add exponential delay.
 * This function will block the calling task for the current timeout value.
 *
 * @param[in, out] reconnectParam structure containing reconnection parameters.
 *
 * @return true after successful sleep, false when all attempts are exhausted.
 */
bool Transport_ReconnectBackoffAndSleep( TransportReconnectParams_t * reconnectParams );

#endif /* ifndef RECONNECT_H_ */
