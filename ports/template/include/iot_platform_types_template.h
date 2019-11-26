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
 * @file iot_platform_types_template.h
 * @brief Template definitions of platform layer types.
 */

#ifndef IOT_PLATFORM_TYPES_TEMPLATE_H_
#define IOT_PLATFORM_TYPES_TEMPLATE_H_

/**
 * @brief Set this to the target system's mutex type.
 */
typedef void * _IotSystemMutex_t;

/**
 * @brief Set this to the target system's semaphore type.
 */
typedef void * _IotSystemSemaphore_t;

/**
 * @brief Set this to the target system's timer type.
 */
typedef void * _IotSystemTimer_t;

/**
 * @brief The format for remote server host and port on this system.
 */
typedef void * _IotNetworkServerInfo_t;

/**
 * @brief The format for network credentials on this system.
 */
typedef void * _IotNetworkCredentials_t;

/**
 * @brief The handle of a network connection on this system.
 */
typedef void * _IotNetworkConnection_t;

#endif /* ifndef IOT_PLATFORM_TYPES_TEMPLATE_H_ */
