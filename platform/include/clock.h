/*
 * IoT Platform V1.1.0
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
 * @file iot_clock.h
 * @brief Time-related functions used by libraries in this SDK.
 */

#ifndef IOT_CLOCK_H_
#define IOT_CLOCK_H_

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * @functionspage{platform_clock,platform clock component,Clock}
 * - @functionname{platform_clock_function_gettimestring}
 */

/**
 * @functionpage{IotClock_GetTimestring,platform_clock,gettimestring}
 */

/**
 * @brief Generates a human-readable timestring, such as "01 Jan 2018 12:00".
 *
 * This function uses the system clock to generate a human-readable timestring.
 * This timestring is printed by the [logging functions](@ref logging_functions).
 *
 * @param[out] pBuffer A buffer to store the timestring in.
 * @param[in] bufferSize The size of `pBuffer`.
 * @param[out] pTimestringLength The actual length of the timestring stored in
 * `pBuffer`.
 *
 * @return `true` if a timestring was successfully generated; `false` otherwise.
 *
 * @warning The implementation of this function must not call any [logging functions]
 * (@ref logging_functions).
 *
 * <b>Example</b>
 * @code{c}
 * char timestring[ 32 ];
 * size_t timestringLength = 0;
 *
 * if( IotClock_GetTimestring( timestring, 32, &timestringLength ) == true )
 * {
 *     printf( "Timestring: %.*s", timestringLength, timestring );
 * }
 * @endcode
 */
/* @[declare_platform_clock_gettimestring] */
bool Clock_GetTimestring( char * pBuffer,
                          size_t bufferSize,
                          size_t * pTimestringLength );

#endif /* ifndef IOT_CLOCK_H_ */
