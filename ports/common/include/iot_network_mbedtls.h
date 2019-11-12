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
 * @file iot_network_mbedtls.h
 * @brief Declares the network stack functions specified in iot_network.h for
 * mbed TLS.
 */

#ifndef IOT_NETWORK_MBEDTLS_H_
#define IOT_NETWORK_MBEDTLS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Platform types include. */
#include "types/iot_platform_types.h"

/* Platform network include. */
#include "platform/iot_network.h"

/**
 * @brief Provides a default value for an #IotNetworkServerInfo.
 *
 * All instances of #IotNetworkServerInfo should be initialized with
 * this constant when using this mbed TLS network stack.
 *
 * @warning Failing to initialize an #IotNetworkServerInfo may result in
 * a crash!
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_SERVER_INFO_MBEDTLS_INITIALIZER    { 0 }

/**
 * @brief Initialize an #IotNetworkCredentials for AWS IoT with ALPN enabled
 * when using this mbed TLS network stack.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define AWS_IOT_NETWORK_CREDENTIALS_MBEDTLS_INITIALIZER \
    {                                                   \
        .pAlpnProtos = "x-amzn-mqtt-ca"                 \
    }

/**
 * @brief Generic initializer for an #IotNetworkCredentials when using this
 * mbed TLS network stack.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_CREDENTIALS_MBEDTLS_INITIALIZER    { 0 }

/**
 * @brief Provides a pointer to an #IotNetworkInterface_t that uses the functions
 * declared in this file.
 */
#define IOT_NETWORK_INTERFACE_MBEDTLS                  ( IotNetworkMbedtls_GetInterface() )

/**
 * @brief Retrieve the network interface using the functions in this file.
 */
const IotNetworkInterface_t * IotNetworkMbedtls_GetInterface( void );

/**
 * @brief One-time initialization function for this network stack.
 *
 * This function performs internal setup of this network stack. <b>It must be
 * called once (and only once) before calling any other function in this network
 * stack</b>. Calling this function more than once without first calling
 * #IotNetworkMbedtls_Cleanup may result in a crash.
 *
 * @return #IOT_NETWORK_SUCCESS or #IOT_NETWORK_FAILURE.
 *
 * @warning No thread-safety guarantees are provided for this function.
 */
IotNetworkError_t IotNetworkMbedtls_Init( void );

/**
 * @brief One-time deinitialization function for this network stack.
 *
 * This function frees resources taken in #IotNetworkMbedtls_Init. It should be
 * called after destroying all network connections to clean up this network
 * stack. After this function returns, #IotNetworkMbedtls_Init must be called
 * again before calling any other function in this network stack.
 *
 * @warning No thread-safety guarantees are provided for this function. Do not
 * call this function if any network connections exist!
 */
void IotNetworkMbedtls_Cleanup( void );

/**
 * @brief An implementation of #IotNetworkInterface_t::create for mbed TLS.
 */
IotNetworkError_t IotNetworkMbedtls_Create( IotNetworkServerInfo_t pServerInfo,
                                            IotNetworkCredentials_t pCredentialInfo,
                                            IotNetworkConnection_t * pConnection );

/**
 * @brief An implementation of #IotNetworkInterface_t::setReceiveCallback for
 * mbed TLS.
 */
IotNetworkError_t IotNetworkMbedtls_SetReceiveCallback( IotNetworkConnection_t pConnection,
                                                        IotNetworkReceiveCallback_t receiveCallback,
                                                        void * pContext );

/**
 * @brief An implementation of #IotNetworkInterface_t::setCloseCallback for
 * mbed TLS.
 */
IotNetworkError_t IotNetworkMbedtls_SetCloseCallback( IotNetworkConnection_t pConnection,
                                                      IotNetworkCloseCallback_t closeCallback,
                                                      void * pContext );

/**
 * @brief An implementation of #IotNetworkInterface_t::send for mbed TLS.
 */
size_t IotNetworkMbedtls_Send( IotNetworkConnection_t pConnection,
                               const uint8_t * pMessage,
                               size_t messageLength );

/**
 * @brief An implementation of #IotNetworkInterface_t::receive for mbed TLS.
 */
size_t IotNetworkMbedtls_Receive( IotNetworkConnection_t pConnection,
                                  uint8_t * pBuffer,
                                  size_t bytesRequested );

/**
 * @brief An implementation of #IotNetworkInterface_t::close for mbed TLS.
 */
IotNetworkError_t IotNetworkMbedtls_Close( IotNetworkConnection_t pConnection );

/**
 * @brief An implementation of #IotNetworkInterface_t::destroy for mbed TLS.
 */
IotNetworkError_t IotNetworkMbedtls_Destroy( IotNetworkConnection_t pConnection );

/**
 * @brief Used by metrics to retrieve the socket (file descriptor) associated with
 * a connection.
 */
int IotNetworkMbedtls_GetSocket( IotNetworkConnection_t pConnection );

#endif /* ifndef IOT_NETWORK_MBEDTLS_H_ */
