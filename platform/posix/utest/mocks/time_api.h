/*
 * AWS IoT Device SDK for Embedded C 202108.00
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
 * @file time_api.h
 * @brief This file is used to generate a mock for any functions from
 * time.h since mocking time.h causes several compilation errors from
 * parsing its macros.
 */

#ifndef TIME_API_H_
#define TIME_API_H_

#include <time.h>

/* Make the process sleep for SECONDS seconds, or until a signal arrives
 * and is not ignored.  The function returns the number of seconds less
 * than SECONDS which it actually slept (thus zero if it slept the full time).
 * If a signal handler does a `longjmp' or modifies the handling of the
 * SIGALRM signal while inside `sleep' call, the handling of the SIGALRM
 * signal afterwards is undefined.  There is no return value to indicate
 * error, but if `sleep' returns SECONDS, it probably didn't work.
 *
 * This function is a cancellation point and therefore not marked with
 * __THROW.  */
extern unsigned int sleep( unsigned int seconds );

/* Get current value of clock CLOCK_ID and store it in the timespec.  */
extern int clock_gettime( clockid_t clock_id,
                          struct timespec * time_point );

/* Pause execution for a number of nanoseconds.
 *
 * This function is a cancellation point and therefore not marked with
 * __THROW.  */
extern int nanosleep( const struct timespec * requested_time,
                      struct timespec * remaining );

#endif /* ifndef TIME_API_ */
