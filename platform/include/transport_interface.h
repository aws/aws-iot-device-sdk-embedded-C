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

/**
 * @file transport_interface.h
 * @brief Transport interface definitions to send and receive data over the
 * network.
 */
#ifndef TRANSPORT_INTERFACE_H_
#define TRANSPORT_INTERFACE_H_

#include <stdint.h>
#include <stddef.h>

/**
 * @page transport_interface Transport Interface
 * @brief The transport interface implementation
 *
 * The transport interface is a set of APIs that must be implemented using an
 * external TCP/IP stack and/or a TLS layer. The transport interface is
 * implemented in @ref transport_interface.h. This interface allows the
 * application layer protocol library to send and receive data over the transport
 * layer. This interface does not handle connection and disconnection to the
 * server of interest. The connection to the server of interest must be made
 * before the library is used with @ref TransportInterface_t. The application is
 * also responsible for disconnection from the server. This interface does not
 * handle socket timeouts or any setup of TLS; these things must be done before
 * using the library's functions that need to send and receive data.
 * <br>
 *
 * The functions that must be implemented are:<br>
 * - [Transport Receive](@ref TransportRecv_t)
 * - [Transport Send](@ref TransportSend_t)
 *
 * Each of the functions above take in an opaque context @ref NetworkContext_t.
 * The functions above and the context are also grouped together in the
 * @ref TransportInterface_t structure:<br><br>
 * @snippet this define_transportinterface
 * <br>
 *
 * The follow steps give guidance on implementing the transport interface.
 *
 * -# Implementing the @ref NetworkContext_t<br><br>
 * @snippet this define_networkcontext
 * <br>
 * @ref NetworkContext_t is an opaque pointer of the incomplete type <b>struct
 * NetworkContext</b>. The struct NetworkContext should contain all the
 * information that is needed to send data with the @ref TransportRecv_t and the
 * @ref TransportSend_t implementations.<br>
 * struct NetworkContext is typically implemented with the TCP socket context
 * and a TLS context.<br><br>
 * <b>Example code:</b>
 * @code{c}
 * struct NetworkContext
 * {
 *     struct MyTCPSocketContext tcpSocketContext;
 *     struct MyTLSContext tlsContext;
 * };
 * @endcode
 * <br>
 * -# Implementing @ref TransportRecv_t<br><br>
 * @snippet this define_transportrecv
 * <br>
 * This callback lets the application know that the library is ready to receive
 * data over the network. Connection with the server of interest should have
 * been made before invoking any library routines that receive data over the
 * network.
 * The @ref TransportRecv_t is typically implemented by calling directly the
 * TLS layer function to receive data. If one is transferring over plain text TCP,
 * without TLS, then a call directly to the TCP layer function to receive data is
 * made.
 * @ref TransportRecv_t may be invoked multiple times by the library if less
 * bytes than were requested to receive are returned.
 * <br><br>
 * <b>Example code:</b>
 * @code{c}
 * int32_t myNetworkRecvImplementation( const NetworkContext_t * pNetworkContext,
 *                                      void * pBuffer,
 *                                      size_t bytesToRecv )
 * {
 *     int32_t bytesReceived = 0;
 *     bytesReceived = mySocketRecv( pNetworkContext->tcpSocketContext,
 *                                   pBuffer,
 *                                   bytesToRecv,
 *                                   MY_SOCKET_TIMEOUT );
 *     if( bytesReceived < 0 )
 *     {
 *         // Handle socket error.
 *     }
 *     // Handle other cases.
 *
 *     return bytesReceived;
 * }
 * @endcode
 * <br>
 * -# Implementing @ref TransportSend_t<br><br>
 * @snippet this define_transportsend
 * <br>
 * This callback lets the application know that the library is ready to send
 * data over the network. Connection with the server of interest should have
 * been made before invoking any library routines that send data over the
 * network.
 * The @ref TransportSend_t is typically implemented by calling directly the
 * TLS layer function to send data. If one is transferring over plain text TCP,
 * without TLS, then a call directly to the TCP layer function to send data is
 * @ref TransportSend_t may be invoked multiple times by the library if less
 * bytes than were requested to send are returned.
 * <br><br>
 * <b>Example code:</b>
 * @code{c}
 * int32_t myNetworkSendImplementation( const NetworkContext_t * pNetworkContext,
 *                                      void * pBuffer,
 *                                      size_t bytesToRecv )
 * {
 *     int32_t bytesSent = 0;
 *     bytesSent = mySocketSend( pNetworkContext->tcpSocketContext,
 *                               pBuffer,
 *                               bytesToRecv,
 *                               MY_SOCKET_TIMEOUT );
 *     if( bytesSent < 0 )
 *     {
 *         // Handle socket error.
 *     }
 *     // Handle other cases.
 *
 *     return bytesSent;
 * }
 * @endcode
 */

/**
 * @transportstruct
 * @typedef NetworkContext_t
 * @brief The NetworkContext is an incomplete type. An implementation of this
 * interface must define struct NetworkContext for their system's requirements.
 * This context is passed into the network interface functions.
 */
/* @[define_networkcontext] */
struct NetworkContext;
typedef struct NetworkContext NetworkContext_t;
/* @[define_networkcontext] */

/**
 * @transportcallback
 * @brief Transport interface for receiving data on the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer to receive the data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return The number of bytes received or a negative error code.
 */
/* @[define_transportrecv] */
typedef int32_t ( * TransportRecv_t )( const NetworkContext_t * pNetworkContext,
                                       void * pBuffer,
                                       size_t bytesToRecv );
/* @[define_transportrecv] */

/**
 * @transportcallback
 * @brief Transport interface for sending data over the network.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return The number of bytes sent or a negative error code.
 */
/* @[define_transportsend] */
typedef int32_t ( * TransportSend_t )( const NetworkContext_t * pNetworkContext,
                                       const void * pBuffer,
                                       size_t bytesToSend );
/* @[define_transportsend] */

/**
 * @transportstruct
 * @brief The transport layer interface.
 */
/* @[define_transportinterface] */
typedef struct TransportInterface
{
    TransportRecv_t recv;               /**< Transport receive interface. */
    TransportSend_t send;               /**< Transport send interface. */
    NetworkContext_t * pNetworkContext; /**< Implementation-defined network context. */
} TransportInterface_t;
/* @[define_transportinterface] */

#endif /* ifndef TRANSPORT_INTERFACE_H_ */
