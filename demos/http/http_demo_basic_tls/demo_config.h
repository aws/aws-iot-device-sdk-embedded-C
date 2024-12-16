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

#ifndef DEMO_CONFIG_H_
#define DEMO_CONFIG_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging config definition and header files inclusion are required in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for DEMO.
 * 3. Include the header file "logging_stack.h", if logging is enabled for DEMO.
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "DEMO"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief HTTP server host name.
 *
 * @note This demo uses httpbin: A simple HTTP Request & Response Service.
 *
 * An httpbin server can be setup locally for running this demo against
 * it. Please refer to the instructions in the README to do so.
 */
#ifndef SERVER_HOST
    #define SERVER_HOST    "localhost"
#endif

/**
 * @brief HTTP server port number.
 *
 * In general, port 443 is for TLS HTTP connections.
 */
#ifndef HTTPS_PORT
    #define HTTPS_PORT    443
#endif

/**
 * @brief Path of the file containing the server's root CA certificate for TLS authentication.
 *
 * @note This certificate should be PEM-encoded.
 */
#ifndef ROOT_CA_CERT_PATH
    #define ROOT_CA_CERT_PATH    "certificates/AmazonRootCA1.crt"
#endif

/**
 * @brief Paths for different HTTP methods for specified host.
 *
 * For httpbin.org, see https://httpbin.org/#/HTTP_Methods for details on
 * supported REST API.
 */
#define GET_PATH                          "/get"
#define HEAD_PATH                         "/get"
#define PUT_PATH                          "/put"
#define POST_PATH                         "/post"

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define USER_BUFFER_LENGTH                ( 2048 )

/**
 * @brief Request body to send for PUT and POST requests in this demo.
 */
#define REQUEST_BODY                      "Hello, world!"

#endif /* ifndef DEMO_CONFIG_H_ */
