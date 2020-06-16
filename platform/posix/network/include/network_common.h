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

#ifndef COMMON_TYPES_H_
#define COMMON_TYPES_H_

#include <stdint.h>
#include <stddef.h>

/**
 * @ingroup platform_datatypes_enums
 * @brief Return codes for [network functions](@ref platform_network_functions).
 */
typedef enum NetworkStatus
{
    NETWORK_SUCCESS = 0,         /**< Function successfully completed. */
    NETWORK_INVALID_PARAMETER,   /**< At least one parameter was invalid. */
    NETWORK_INVALID_CREDENTIALS, /**< Provided certificates or key were invalid. */
    NETWORK_CONNECT_FAILURE,     /**< Initial connection to the server failed. */
    NETWORK_DNS_FAILURE,         /**< Resolving hostname of server failed. */
    NETWORK_INTERNAL_ERROR,      /**< Generic failure not covered by other values. */
    NETWORK_NO_MEMORY,           /**< Memory allocation failed. */
    NETWORK_SYSTEM_ERROR         /**< An error occurred when calling a system API. */
} NetworkStatus_t;

/**
 * @ingroup platform_datatypes_enums
 * @brief Disconnect reasons for [the network close callback](@ref platform_network_function_closecallback).
 */
typedef enum NetworkCloseReason
{
    NETWORK_NOT_CLOSED = 0,    /**< Not closed, still open */
    NETWORK_SERVER_CLOSED,     /**< Server closed connection. */
    NETWORK_TRANSPORT_FAILURE, /**< Transport failed. */
    NETWORK_CLIENT_CLOSED,     /**< Client closed connection. */
    NETWORK_UNKNOWN_CLOSED     /**< Unknown close reason. */
} NetworkCloseReason_t;

#endif /* ifndef COMMON_TYPES_H_ */
