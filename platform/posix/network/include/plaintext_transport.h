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

#ifndef PLAINTEXT_CONFIG_H_
#define PLAINTEXT_CONFIG_H_

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
    #define LIBRARY_LOG_NAME     "Plaintext Transport"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

#include "network_interface.h"

/**
 * @brief Definition of the network context.
 *
 * @note An integer is used to store the descriptor of the socket.
 */
struct NetworkContext
{
    int tcpSocket;
};

/**
 * @brief Set timeout for transport send.
 *
 * @brief param[in] timeout The timeout to set for transport send.
 */
void setSendTimeout( int timeout );

/**
 * @brief Set timeout for transport recv.
 *
 * @brief param[in] timeout The timeout to set for transport recv.
 */
void setRecvTimeout( int timeout );

/**
 * @brief The transport send function that defines the transport interface.
 *
 * This is passed as the #TransportInterface.send function and used to
 * send data over the network.
 *
 * @param[in] pContext User defined context (TCP socket and SSL context for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Number of bytes sent if successful; otherwise negative value on error.
 */
int32_t Plaintext_Send( NetworkContext_t pContext,
                        const void * pBuffer,
                        size_t bytesToSend );

/**
 * @brief The transport receive function that defines the transport interface.
 *
 * This is passed as the #TransportInterface.recv function used for reading
 * data received from the network.
 *
 * @param[in] pContext User defined context (TCP socket and SSL context for this demo).
 * @param[out] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return Number of bytes received if successful; otherwise negative value on error.
 */
int32_t Plaintext_Recv( NetworkContext_t pContext,
                        void * pBuffer,
                        size_t bytesToRecv );

#endif /* ifndef PLAINTEXT_CONFIG_H_ */
