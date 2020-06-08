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

#ifndef DEMO_CONFIG_H_
#define DEMO_CONFIG_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging related header files are required to be included in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define LIBRARY_LOG_NAME and  LIBRARY_LOG_LEVEL.
 * 3. Include the header file "logging_stack.h".
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Demo. */
#define LIBRARY_LOG_NAME     "DEMO"
#define LIBRARY_LOG_LEVEL    LOG_INFO

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief HTTP server host name.
 *
 * @note A local HTTP server is used for this demo. Instructions for setting
 * this up can be found in the top-level README.md file.
 */
#define SERVER_HOST    "localhost"

/**
 * @brief HTTP server port number.
 *
 * @note In general, port 80 is for plaintext HTTP connections. However,
 * the default plaintext port from the local http server is used below.
 */
#define SERVER_PORT    8080

/**
 * @brief Paths for different HTTP methods for specified host.
 */
#ifndef GET_PATH
    #define GET_PATH    "/get"
#endif

#ifndef HEAD_PATH
    #define HEAD_PATH    "/get"
#endif

#ifndef PUT_PATH
    #define PUT_PATH    "/put"
#endif

#ifndef POST_PATH
    #define POST_PATH    "/post"
#endif

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define USER_BUFFER_LENGTH                ( 1024 )

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LEN           ( 40 )

/**
 * @brief Request body to send for PUT and POST requests in this demo.
 */
#define REQUEST_BODY                      "Hello, world!"

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH               ( sizeof( REQUEST_BODY ) - 1 )

#endif /* ifndef DEMO_CONFIG_H */
