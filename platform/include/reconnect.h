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
 * @brief Declaration of the backoff logic when connection fails to the server fails.
 */


/* bools are only defined in C99+ */
#if defined( __cplusplus ) || __STDC_VERSION__ >= 199901L
    #include <stdbool.h>
#elif !defined( bool )
    #define bool     signed char
    #define false    0
    #define true     1
#endif

#define MAX_RECONNECT_ATTEMPS                5
#define RECONNECT_INITIAL_TIMEOUT_SECONDS    2

/**
 * @brief Reset reconnection timer. This must be called by the application 
 * everytime when application wants to start new connection with the server. 
 */
void reconnectBackoffReset();

/**
 * @brief Very simple platfrom specific exponential backoff function. The application
 * must use this function while connecting to a server to handle connection failures.
 *
 * @return true after successful sleep, false when all attempts are exhausted.
 */
bool reconnectBackoffAndSleep();