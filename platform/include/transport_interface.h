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

#ifndef TRANSPORT_INTERFACE_H_
#define TRANSPORT_INTERFACE_H_

#include <stdint.h>
#include <stddef.h>

/**
 * @brief The NetworkContext is an incomplete type. The application must
 * define NetworkContext to the type of their network context. This context
 * is passed into the network interface functions.
 */
struct NetworkContext;
typedef struct NetworkContext * NetworkContext_t;

/**
 * @brief Transport interface for reading data on the network.
 *
 * @param[in] pNetworkContext Application-defined context.
 * @param[in] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return The number of bytes read or a negative error code.
 */
typedef int32_t ( * TransportRecv_t )( NetworkContext_t pNetworkContext,
                                       void * pBuffer,
                                       size_t bytesToRead );

/**
 * @brief Transport interface for sending data over the network.
 *
 * @param[in] pNetworkContext Application-defined context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to write to the network.
 *
 * @return The number of bytes written or a negative error code.
 */
typedef int32_t ( * TransportSend_t )( NetworkContext_t pNetworkContext,
                                       const void * pBuffer,
                                       size_t bytesToSend );

/**
 * @brief The transport layer interface.
 */
typedef struct TransportInterface
{
    TransportRecv_t recv;             /**< Transport receive interface. */
    TransportSend_t send;             /**< Transport send interface. */
    NetworkContext_t pNetworkContext; /**< Application-defined transport interface context. */
} TransportInterface_t;

#endif /* ifndef TRANSPORT_INTERFACE_H_ */
