/*
 * SigV4 Utility Library v1.0.0
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
 * @file sigv4_config.h
 * @brief Values for configuration macros provided by the application to be
 * used by the SigV4 Utility Library.
 */

#ifndef SIGV4_CONFIG_H_
#define SIGV4_CONFIG_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Include logging header files and define logging macros in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for SIGV4.
 * 3. Include the header file "logging_stack.h", if logging is enabled for SIGV4.
 */

#include "logging_levels.h"

/* Logging configuration for the SigV4 library. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "SIGV4"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/**
 * @brief The size of the compile time allocated internal library buffer that is used
 * for generating the canonical request.
 */
#define SIGV4_PROCESSING_BUFFER_LENGTH    4096U

/**
 * @brief Number of HTTP headers does not exceed a maximum of 10 in HTTP requests sent to S3
 * for the demo application.
 */
#define SIGV4_MAX_HTTP_HEADER_COUNT       10U

/**
 * @brief Query parameters used in requests to S3.
 */
#define SIGV4_MAX_QUERY_PAIR_COUNT        100U

/**
 * @brief Setting SIGV4_USE_CANONICAL_SUPPORT to 1 as the HTTP request is not pre-canonicalized
 * in the demo application.
 */
#define SIGV4_USE_CANONICAL_SUPPORT       1

#endif /* ifndef SIGV4_CONFIG_H_ */
