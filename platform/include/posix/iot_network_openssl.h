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

#ifndef _IOT_NETWORK_OPENSSL_H_
#define _IOT_NETWORK_OPENSSL_H_

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* POSIX types include. */
#ifdef POSIX_TYPES_HEADER
    #include POSIX_TYPES_HEADER
#else
    #include <sys/types.h>
#endif

/* Standard bool include. */
#include <stdbool.h>

/* OpenSSL types include. */
#include <openssl/ossl_typ.h>

/* Platform types include. */
#include "types/iot_platform_types.h"

/* Platform network include. */
#include "platform/iot_network.h"

/**
 * @brief Represents a network connection that uses OpenSSL.
 *
 * All instances of #IotNetworkConnectionOpenssl_t should be initialized with
 * #IOT_NETWORK_CONNECTION_OPENSSL_INITIALIZER.
 *
 * @attention The members of this struct are intended to be opaque and may change
 * at any time. This struct should only be passed as the connection handle to the
 * functions declared in this file. Do not directly modify its members!
 */
typedef struct IotNetworkConnectionOpenssl
{
    int socket;        /**< @brief Socket associated with this connection. */
    SSL * pSslContext; /**< @brief SSL context for connection. */
    IotMutex_t mutex;  /**< @brief Synchronizes the various network threads. */

    /** @brief Status of the receive thread for this connection. */
    enum
    {
        _NONE = 0, _ACTIVE, _TERMINATED
    } receiveThreadStatus;
    pthread_t receiveThread;                     /**< @brief Thread that handles receiving on this connection. */

    IotNetworkReceiveCallback_t receiveCallback; /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                      /**< @brief The context for the receive callback. */
} IotNetworkConnectionOpenssl_t;

/**
 * @brief Information on the remote server for connection setup.
 *
 * Passed to #IotNetworkOpenssl_Create as `pConnectionInfo`.
 *
 * All instances of #IotNetworkServerInfoOpenssl_t should be initialized with
 * #IOT_NETWORK_SERVER_INFO_OPENSSL_INITIALIZER.
 */
typedef struct IotNetworkServerInfoOpenssl
{
    const char * pHostName; /**< @brief Server host name. Must be NULL-terminated. */
    uint16_t port;          /**< @brief Server port in host-order. */
} IotNetworkServerInfoOpenssl_t;

/**
 * @brief Contains the credentials necessary for connection setup with OpenSSL.
 *
 * Passed to #IotNetworkOpenssl_Create as `pCredentialInfo`.
 *
 * All instances of #IotNetworkCredentialsOpenssl_t should be initialized with either
 * #AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER (for connections to AWS IoT) or
 * #IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER (for other connections).
 */
typedef struct IotNetworkCredentialsOpenssl
{
    /**
     * @brief Set this to a non-NULL value to use ALPN.
     *
     * This string must be NULL-terminated.
     *
     * See [this link]
     * (https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/)
     * for more information.
     */
    const char * pAlpnProtos;

    /**
     * @brief Set this to a non-zero value to use TLS max fragment length
     * negotiation (TLS MFLN).
     *
     * @note OpenSSL may have a minimum value for this parameter;
     * #IotNetworkOpenssl_Create may return an error if this parameter is too small.
     */
    size_t maxFragmentLength;

    /**
     * @brief Disable server name indication (SNI) for a TLS session.
     */
    bool disableSni;

    /* These paths must be NULL-terminated. */
    const char * pRootCaPath;     /**< @brief Filesystem path of a trusted server root certificate. */
    const char * pClientCertPath; /**< @brief Filesystem path of the client certificate. */
    const char * pPrivateKeyPath; /**< @brief Filesystem path of the client certificate's private key. */
} IotNetworkCredentialsOpenssl_t;

/**
 * @brief Provides a default value for an #IotNetworkConnectionOpenssl_t.
 *
 * All instances of #IotNetworkConnectionOpenssl_t should be initialized with
 * this constant.
 *
 * @warning Failing to initialize an #IotNetworkConnectionOpenssl_t with this
 * initializer may result in undefined behavior!
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_CONNECTION_OPENSSL_INITIALIZER     { 0 }

/**
 * @brief Provides a default value for an #IotNetworkServerInfoOpenssl_t.
 *
 * All instances of #IotNetworkServerInfoOpenssl_t should be initialized with
 * this constant.
 *
 * @warning Failing to initialize an #IotNetworkServerInfoOpenssl_t with this
 * initializer may result in undefined behavior!
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_SERVER_INFO_OPENSSL_INITIALIZER    { 0 }

/**
 * @brief Initialize an #IotNetworkCredentialsOpenssl_t for AWS IoT with ALPN enabled.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER \
    {                                                   \
        .pAlpnProtos = "\x0ex-amzn-mqtt-ca"             \
    }

/**
 * @brief Generic initializer for an #IotNetworkCredentialsOpenssl_t.
 *
 * @note This initializer may change at any time in future versions, but its
 * name will remain the same.
 */
#define IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER    { 0 }

/**
 * @brief Provides a pointer to an #IotNetworkInterface_t that uses the functions
 * declared in this file.
 */
#define IOT_NETWORK_INTERFACE_OPENSSL                  ( &( _IotNetworkOpenssl ) )

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
                                            void * const pConnection );

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
                                  uint8_t * const pBuffer,
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
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Declaration of a network interface struct using the functions in this file.
 */
extern const IotNetworkInterface_t _IotNetworkOpenssl;
/** @endcond */

#endif /* ifndef _IOT_NETWORK_OPENSSL_H_ */
