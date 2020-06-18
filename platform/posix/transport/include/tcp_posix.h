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

#ifndef TCP_POSIX_H_
#define TCP_POSIX_H_

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
    #define LIBRARY_LOG_NAME     "TCP Posix"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/* Transport interface include. */
#include "transport_interface.h"

/**
 * @brief TCP Connect / Disconnect return status.
 */
typedef enum TCPStatus
{
    TCP_SUCCESS = 0,       /**< Function successfully completed. */
    TCP_INVALID_PARAMETER, /**< At least one parameter was invalid. */
    TCP_DNS_FAILURE,       /**< Resolving hostname of server failed. */
    TCP_CONNECT_FAILURE    /**< Initial connection to the server failed. */
} TCPStatus_t;

/**
 * @brief End connection to server.
 *
 * @brief param[in] pServerInfo Server host name.
 * @brief param[in] hostNameLength Length associated with host name.
 * @brief param[in] port Server port in host-order.
 * @brief param[out] pTcpSocket Pointer to the socket descriptor.
 *
 * @return #TCP_SUCCESS if successful;
 * #TCP_INVALID_PARAMETER, #TCP_DNS_FAILURE, #TCP_CONNECT_FAILURE on error.
 */
TCPStatus_t TCP_Connect( const char * pHostName,
                         size_t hostNameLength,
                         uint16_t port,
                         int * pTcpSocket );

/**
 * @brief End connection to server.
 *
 * @brief param[in] tcpSocket The socket descriptor.
 */
void TCP_Disconnect( int tcpSocket );

/**
 * @brief Set timeout for transport recv.
 *
 * @brief param[in] timeout The timeout to set for transport recv.
 */
void TCP_SetRecvTimeout( int timeout );

/**
 * @brief Set timeout for transport send.
 *
 * @brief param[in] timeout The timeout to set for transport send.
 */
void TCP_SetSendTimeout( int timeout );

/**
 * @brief The transport receive function that defines the transport interface.
 *
 * This is passed as the #TransportInterface.recv function used for reading
 * data received from the network.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[out] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return Number of bytes received if successful; otherwise negative value on error.
 */
int32_t TCP_Recv( NetworkContext_t pContext,
                  void * pBuffer,
                  size_t bytesToRecv );

/**
 * @brief The transport send function that defines the transport interface.
 *
 * This is passed as the #TransportInterface.send function and used to
 * send data over the network.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Number of bytes sent if successful; otherwise negative value on error.
 */
int32_t TCP_Send( NetworkContext_t pContext,
                  const void * pBuffer,
                  size_t bytesToSend );

#endif /* ifndef TCP_POSIX_H_ */
