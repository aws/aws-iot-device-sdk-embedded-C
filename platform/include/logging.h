/*
 * IoT Common V1.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_logging.h
 * @brief Generic logging function header file.
 *
 * Declares the generic logging function.
 *
 * @see iot_logging_setup.h
 */

#ifndef IOT_LOGGING_H_
#define IOT_LOGGING_H_

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * @functionspage{logging,logging library}
 *
 * - @functionname{logging_function_generic}
 */

/**
 * @functionpage{Log_Generic,logging,generic}
 */

/**
 * @brief Generic logging function that prints a single message.
 *
 * This function represents a reference implementation for the
 * @ref logging_function_log logging interface.
 *
 * @param[in] messageLevel The log level of the this message. See @ref LIBRARY_LOG_LEVEL.
 * @param[in] pFormat Format string for the log message.
 * @param[in] ... Arguments for format specification.
 *
 * @return No return value. On errors, it prints nothing.
 */
/* @[declare_logging_generic] */
void Log_Generic( int32_t messageLevel,
                  const char * const pFormat,
                  ... );
/* @[declare_logging_generic] */


#endif /* ifndef IOT_LOGGING_H_ */
