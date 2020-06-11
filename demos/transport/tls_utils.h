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
 * @file tls_utils.h
 * @brief Wrapper utilities for using OpenSSL based TLS stack for demos and
 * integration tests.
 */

#ifndef TLS_UTILS_H_
#define TLS_UTILS_H_

/* OpenSSL include. */
#include <openssl/ssl.h>

#include "mqtt.h"

/**
 * @brief Creates a TCP connection to the MQTT broker as specified by
 * BROKER_ENDPOINT and BROKER_PORT defined at the top of this file.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 * @param[out] pTcpSocket Pointer to TCP socket file descriptor.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
int tcpConnectToServer( const char * pServer,
                        uint16_t port,
                        int * pTcpSocket );

/**
 * @brief Closes a TCP connection with a server, if valid.
 *
 * @param[in] tcpSocket The socket for the TCP connection.
 */
void closeTcpConnection( int tcpSocket );

/**
 * @brief Set up a TLS connection over an existing TCP connection.
 *
 * @param[in] tcpSocket Existing TCP connection.
 * @param[out] pSslContext Pointer to SSL connection context pointer.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
int tlsSetup( int tcpSocket,
              SSL ** pSslContext );

/**
 * @brief Closes an established TLS session.
 *
 * @param[in] pSSlContext The SSL context associated with the TLS session.
 */
void closeTlsSession( SSL * pSslContext );

/**
 * @brief The transport send function provided to the MQTT context.
 *
 * @param[in] pSslContext Pointer to SSL context.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToSend Length of data to send.
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
int32_t transportSend( MQTTNetworkContext_t pSslContext,
                       const void * pMessage,
                       size_t bytesToSend );

/**
 * @brief The transport receive function provided to the MQTT context.
 *
 * @param[in] pSslContext Pointer to SSL context.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToRecv Length of data to be received.
 *
 * @return Number of bytes received; negative value on error;
 * 0 for timeout.
 */
int32_t transportRecv( MQTTNetworkContext_t pSslContext,
                       void * pBuffer,
                       size_t bytesToRecv );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * This function returns the elapsed time with reference to #globalEntryTimeMs.
 *
 * @return Time in milliseconds.
 */
uint32_t getTimeMs( void );

#endif /* ifndef TLS_UTILS_H_ */
