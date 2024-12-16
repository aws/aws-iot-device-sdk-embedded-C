/*
 * AWS IoT Device SDK for Embedded C 202412.00
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

#ifndef HTTP_DEMO_UTILS_H_
#define HTTP_DEMO_UTILS_H_

/* Standard includes. */
#include <stdlib.h>
#include <stdbool.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Transport interface include. */
#include "transport_interface.h"

/* Other HTTP utils header. */
#include "http_demo_url_utils.h"

/**
 * @brief Function pointer for establishing connection to a server.
 *
 * @param[out] pNetworkContext Implementation-defined network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
typedef int32_t ( * TransportConnect_t )( NetworkContext_t * pNetworkContext );

/**
 * @brief Connect to a server with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increase until maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[in] connectFunction Function pointer for establishing connection to a server.
 * @param[out] pNetworkContext Implementation-defined network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
int32_t connectToServerWithBackoffRetries( TransportConnect_t connectFunction,
                                           NetworkContext_t * pNetworkContext );

/**
 * @brief Get the starting location of HTTP header in an HTTP request.
 *
 * @param[in] requestHeaders HTTP request headers that contains the HTTP request information.
 * @param[out] pStartHeaderLoc Buffer to store the start Location of the HTTP header.
 * @param[out] pHeadersDataLen Length of @p pStartHeaderLoc.
 */
void getHeaderStartLocFromHttpRequest( HTTPRequestHeaders_t requestHeaders,
                                       char ** pStartHeaderLoc,
                                       size_t * pHeadersDataLen );

/**
 * @brief Get the current time in milliseconds.
 *
 * @return Time in milliseconds.
 */
uint32_t getTimeMs( void );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef HTTP_DEMO_UTILS_H_ */
