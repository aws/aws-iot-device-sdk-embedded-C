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

#ifndef CONNECT_H_
#define CONNECT_H_

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
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "TCP"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

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

/**
 * @brief Information on the remote server for connection setup.
 *
 * May be passed to #IotNetworkInterface_t.create as `pConnectionInfo`. This
 * structure contains commonly-used parameters, but may be replaced with an
 * alternative.
 */
typedef struct NetworkServerInfo
{
    const char * pHostName; /**< @brief Server host name. Must be NULL-terminated. */
    size_t hostNameLength;  /**< @brief Length associated with #NetworkServerInfo.pHostName. */
    uint16_t port;          /**< @brief Server port in host-order. */
} NetworkServerInfo_t;

NetworkStatus_t TCP_Connect( int * pTcpSocket,
                             const NetworkServerInfo_t * pServerInfo );
void TCP_Disconnect( int tcpSocket );

#endif /* ifndef CONNECT_H_ */
