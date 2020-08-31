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
 * @file iot_network_openssl.h
 * @brief Declares the network stack functions specified in iot_network.h for
 * POSIX systems with OpenSSL.
 */

#ifndef IOT_NETWORK_OPENSSL_H_
#define IOT_NETWORK_OPENSSL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard bool include. */
#include <stdbool.h>

/* Platform types include. */
#include "types/iot_platform_types.h"

/* Platform network include. */
#include "platform/iot_network.h"

/**
 * @brief Represents a network connection that uses OpenSSL.
 *
 * This is an incomplete type. In application code, only pointers to this type
 * should be used.
 */
typedef struct _networkConnection IotNetworkConnectionOpenssl_t;

/**
 * @brief Provides a default value for an #IotNetworkServerInfo_t.
 *
 * All instances of #IotNetworkServerInfo_t should be initialized with
 * this constant when using this OpenSSL network stack.
 *
 * @warning Failing to initialize an #IotNetworkServerInfo_t may result in
 * a crash!
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_SERVER_INFO_OPENSSL_INITIALIZER    { 0 }

/**
 * @brief Initialize an #IotNetworkCredentials_t for AWS IoT with ALPN enabled
 * when using this OpenSSL network stack.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER \
    {                                                   \
        .pAlpnProtos = "\x0ex-amzn-mqtt-ca"             \
    }

/**
 * @brief Generic initializer for an #IotNetworkCredentials_t when using this
 * OpenSSL network stack.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER    { 0 }

/**
 * @brief Provides a pointer to an #IotNetworkInterface_t that uses the functions
 * declared in this file.
 */
#define IOT_NETWORK_INTERFACE_OPENSSL                  ( IotNetworkOpenssl_GetInterface() )

/**
 * @brief Retrieve the network interface using the functions in this file.
 */
const IotNetworkInterface_t * IotNetworkOpenssl_GetInterface( void );

/**
 * @brief One-time initialization function for this network stack.
 *
 * This function performs internal setup of this network stack. <b>It must be
 * called once (and only once) before calling any other function in this network
 * stack</b>. Calling this function more than once without first calling
 * #IotNetworkOpenssl_Cleanup may result in a crash.
 *
 * @return #IOT_NETWORK_SUCCESS or #IOT_NETWORK_FAILURE.
 *
 * @warning No thread-safety guarantees are provided for this function.
 */
IotNetworkError_t IotNetworkOpenssl_Init( void );

/**
 * @brief One-time deinitialization function for this network stack.
 *
 * This function frees resources taken in #IotNetworkOpenssl_Init. It should be
 * called after destroying all network connections to clean up this network
 * stack. After this function returns, #IotNetworkOpenssl_Init must be called
 * again before calling any other function in this network stack.
 *
 * @warning No thread-safety guarantees are provided for this function. Do not
 * call this function if any network connections exist!
 */
void IotNetworkOpenssl_Cleanup( void );

/**
 * @brief An implementation of #IotNetworkInterface_t::create for POSIX systems
 * with OpenSSL.
 */
IotNetworkError_t IotNetworkOpenssl_Create( void * pConnectionInfo,
                                            void * pCredentialInfo,
                                            void ** pConnection );

/**
 * @brief An implementation of #IotNetworkInterface_t::setReceiveCallback for
 * POSIX systems with OpenSSL.
 */
IotNetworkError_t IotNetworkOpenssl_SetReceiveCallback( void * pConnection,
                                                        IotNetworkReceiveCallback_t receiveCallback,
                                                        void * pContext );

/**
 * @brief An implementation of #IotNetworkInterface_t::send for POSIX systems
 * with OpenSSL.
 */
size_t IotNetworkOpenssl_Send( void * pConnection,
                               const uint8_t * pMessage,
                               size_t messageLength );

/**
 * @brief An implementation of #IotNetworkInterface_t::receive for POSIX systems
 * with OpenSSL.
 */
size_t IotNetworkOpenssl_Receive( void * pConnection,
                                  uint8_t * pBuffer,
                                  size_t bytesRequested );

/**
 * @brief An implementation of #IotNetworkInterface_t::close for POSIX systems
 * with OpenSSL.
 */
IotNetworkError_t IotNetworkOpenssl_Close( void * pConnection );

/**
 * @brief An implementation of #IotNetworkInterface_t::destroy for POSIX systems
 * with OpenSSL.
 */
IotNetworkError_t IotNetworkOpenssl_Destroy( void * pConnection );

/**
 * @brief Used by metrics to retrieve remote server and port of a connection.
 */
void IotNetworkOpenssl_GetServerInfo( void * pConnection,
                                      IotMetricsTcpConnection_t * pServerInfo );

#endif /* ifndef IOT_NETWORK_OPENSSL_H_ */
