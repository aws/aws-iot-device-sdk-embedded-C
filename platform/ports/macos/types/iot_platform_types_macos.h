/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_platform_types_macos.h
 * @brief Definitions of platform layer types on macOS systems.
 */

#ifndef IOT_PLATFORM_TYPES_MACOS_H_
#define IOT_PLATFORM_TYPES_MACOS_H_

/* POSIX includes that are available on macOS. */
#ifdef POSIX_TYPES_HEADER
    #include POSIX_TYPES_HEADER
#else
    #include <sys/types.h>
#endif

/* Grand Central Dispatch include. */
#include <dispatch/dispatch.h>

/* Dispatch blocks API include. */
#include <Block.h>

/**
 * @brief The native mutex type on macOS systems.
 *
 * macOS provides POSIX mutexes.
 */
typedef pthread_mutex_t _IotSystemMutex_t;

/**
 * @brief The native semaphore type on macOS systems.
 *
 * macOS provides a partial implementation of POSIX semaphores, but it does not
 * provide all of the functions needed by this SDK. Grand Central Dispatch
 * semaphores are used instead.
 */
typedef struct _IotSystemSemaphore
{
    uint32_t count;                 /**< @brief The current count of the semaphore. */
    dispatch_semaphore_t semaphore; /**< @brief Grand Central Dispatch semaphore. */
} _IotSystemSemaphore_t;

/**
 * @brief The native timer type on macOS systems.
 *
 * POSIX timers are not available on macOS, so a timer implementation based on
 * Grand Central Dispatch is used instead.
 */
typedef struct _IotSystemTimer
{
    dispatch_block_t dispatchBlock;     /**< @brief A dispatch block that executes for the timer. */
    uint32_t periodMs;                  /**< @brief Expiration period of this timer, if any. */
    void * pArgument;                   /**< @brief First argument to threadRoutine. */
    void ( * threadRoutine )( void * ); /**< @brief Thread function to run on timer expiration. */
} _IotSystemTimer_t;

#endif /* ifndef IOT_PLATFORM_TYPES_MACOS_H_ */
