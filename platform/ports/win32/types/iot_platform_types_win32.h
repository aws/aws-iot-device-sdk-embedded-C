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
 * @file iot_platform_types_win32.h
 * @brief Definitions of platform layer types on Win32 systems.
 */

#ifndef IOT_PLATFORM_TYPES_WIN32_H_
#define IOT_PLATFORM_TYPES_WIN32_H_

/* Standard includes. */
#include <stdint.h>

/* Win32 includes. WinSock2 is needed to prevent the usage of the WinSock
 * header in Windows.h */
#include <WinSock2.h>
#include <ws2tcpip.h>
#include <Windows.h>

/**
 * @brief The "mutex" type on Win32 systems.
 *
 * The Win32 critical section object is used in place of mutex because it
 * consumes less resources and does not need to be shared between processes.
 */
typedef CRITICAL_SECTION _IotSystemMutex_t;

/**
 * @brief The semaphore type on Win32 systems.
 *
 * Because the Win32 API does not provide a way to obtain a semaphore count,
 * the count must be tracked with the semaphore. As noted by the API documentation,
 * semaphore count should not be relied on as it may change before it can be tested.
 * Semaphore count is currently only used in tests.
 */
typedef struct _IotSystemSemaphore
{
    uint32_t count;              /**< @brief The current count of the semaphore. */
    HANDLE semaphore;            /**< @brief Handle to the Win32 semaphore. */
} _IotSystemSemaphore_t;

/**
 * @brief Represents an #IotTimer_t on Win32 systems.
 */
typedef struct _IotSystemTimer
{
    HANDLE timer;                       /**< @brief Handle of the Win32 timer. */
    void * pArgument;                   /**< @brief First argument to threadRoutine. */
    void ( * threadRoutine )( void * ); /**< @brief Thread function to run on timer expiration. */
} _IotSystemTimer_t;

#endif /* ifndef IOT_PLATFORM_TYPES_WIN32_H_ */
