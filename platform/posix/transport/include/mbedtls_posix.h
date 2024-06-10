/*
 * AWS IoT Device SDK for Embedded C 202211.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef MBEDTLS_POSIX_H_
#define MBEDTLS_POSIX_H_

/**
 * @file mbedtls_posix.h
 *
 * @brief Implementation for the transport interface using a mutually
 * authenticated TLS connection with MbedTLS for TLS and core for secure
 * credential management.
 */

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

/* Logging configuration for the transport interface implementation which uses
 * MbedTLS and Sockets. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "Transport_MbedTLS_"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_WARN
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Standard includes. */
#include <stdbool.h>

#define MBEDTLS_ALLOW_PRIVATE_ACCESS

/* MbedTLS includes. */
#include "mbedtls/net_sockets.h"
#include "mbedtls/ssl.h"
#include "mbedtls/pk.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"

/* Transport interface include. */
#include "transport_interface.h"

/**
 * @brief Debug logging level to use for MbedTLS.
 *
 * @note The default value of 0 disables MbedTLS logging.
 * See https://tls.mbed.org/api/debug_8h.html#a6629362e96b43725ace95c8ff01d9985
 * for valid values.
 */
#define MBEDTLS_DEBUG_LOG_LEVEL    4

/**
 * @brief Context containing state for the MbedTLS and core based
 * transport interface implementation.
 *
 * @note Applications using this transport interface implementation should use
 * this struct as the #NetworkContext_t for the transport interface
 * configuration passed to coreMQTT or coreHTTP.
 */
typedef struct MbedtlsContext
{
    mbedtls_net_context socketContext;    /**< @brief MbedTLS socket context. */
    mbedtls_ssl_config config;            /**< @brief SSL connection configuration. */
    mbedtls_ssl_context context;          /**< @brief SSL connection context */
    mbedtls_x509_crt_profile certProfile; /**< @brief Certificate security profile for this connection. */
    mbedtls_x509_crt rootCa;              /**< @brief Root CA certificate context. */
    mbedtls_x509_crt clientCert;          /**< @brief Client certificate context. */
    mbedtls_pk_context privKey;           /**< @brief Client private key context. */
    mbedtls_entropy_context entropyCtx;   /**< @brief Entropy context */
    mbedtls_ctr_drbg_context ctrDrbgCtx;  /**< @brief Random number generator context */
} MbedtlsContext_t;

/**
 * @brief TLS Connect / Disconnect return status.
 */
typedef enum MbedtlsStatus
{
    MBEDTLS_SUCCESS = 0,         /**< Function successfully completed. */
    MBEDTLS_INVALID_PARAMETER,   /**< At least one parameter was invalid. */
    MBEDTLS_INSUFFICIENT_MEMORY, /**< Insufficient memory required to establish connection. */
    MBEDTLS_INVALID_CREDENTIALS, /**< Provided credentials were invalid. */
    MBEDTLS_HANDSHAKE_FAILED,    /**< Performing TLS handshake with server failed. */
    MBEDTLS_INTERNAL_ERROR,      /**< A call to a system API resulted in an internal error. */
    MBEDTLS_CONNECT_FAILURE      /**< Initial connection to the server failed. */
} MbedtlsStatus_t;

/**
 * @brief Contains the credentials necessary for tls connection setup.
 */
typedef struct MbedtlsCredentials
{
    /**
     * @brief To use ALPN, set this to a NULL-terminated list of supported
     * protocols in decreasing order of preference.
     *
     * See [this link]
     * (https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/)
     * for more information.
     */
    const char ** pAlpnProtos;

    /**
     * @brief Disable server name indication (SNI) for a TLS session.
     */
    bool disableSni;

    const char * pRootCaPath;     /**< @brief String representing a trusted server root certificate. */
    const char * pClientCertPath; /**< @brief String representing the PKCS #11 label for the client certificate. */
    const char * pPrivateKeyPath; /**< @brief String representing the PKCS #11 label for the private key. */
} MbedtlsCredentials_t;

/**
 * @brief Sets up a mutually authenticated TLS session on top of a TCP
 * connection using the MbedTLS library for TLS and the core library for
 * credential management.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 * @param[in] pHostName The hostname of the remote endpoint.
 * @param[in] port The destination port.
 * @param[in] pMbedtlsCredentials Credentials for the TLS connection.
 * @param[in] recvTimeoutMs The timeout for socket receive operations.
 *
 * @note #recvTimeoutMs sets the maximum blocking time of the #Mbedtls_Recv function.
 *
 * @return #MBEDTLS_SUCCESS on success;
 * #MBEDTLS_INSUFFICIENT_MEMORY, #MBEDTLS_INVALID_CREDENTIALS,
 * #MBEDTLS_HANDSHAKE_FAILED, #MBEDTLS_INTERNAL_ERROR,
 * or #MBEDTLS_CONNECT_FAILURE on failure.
 */
MbedtlsStatus_t Mbedtls_Connect( NetworkContext_t * pNetworkContext,
                                 const char * pHostName,
                                 uint16_t port,
                                 const MbedtlsCredentials_t * pMbedtlsCredentials,
                                 uint32_t recvTimeoutMs );

/**
 * @brief Gracefully disconnect an established TLS connection.
 *
 * @param[in] pNetworkContext Network context.
 */
void Mbedtls_Disconnect( NetworkContext_t * pNetworkContext );

/**
 * @brief Receives data over an established TLS session using the MbedTLS API.
 *
 * This function can be used as the #TransportInterface.recv implementation of
 * the transport interface to receive data from the network.
 *
 * @param[in] pNetworkContext The network context created using Mbedtls_Connect API.
 * @param[out] pBuffer Buffer to receive network data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return Number of bytes received if successful; negative value to indicate failure.
 * A return value of zero represents that the receive operation can be retried.
 */
int32_t Mbedtls_Recv( NetworkContext_t * pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv );

/**
 * @brief Sends data over an established TLS session using the MbedTLS API.
 *
 * This function can be used as the #TransportInterface.send implementation of
 * the transport interface to send data over the network.
 *
 * @param[in] pNetworkContext The network context created using Mbedtls_Connect API.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Number of bytes sent if successful; negative value on error.
 *
 * @note This function does not return zero value because it cannot be retried
 * on send operation failure.
 */
int32_t Mbedtls_Send( NetworkContext_t * pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend );

/**
 * @brief Generate a new EC Private Key
 * This function generates a new EC private key and writes the resulting key
 * in DER format to the provided path.
 *
 * @param[in] pPrivateKeyPath Path to store the resulting private key.
 *
 * @return #MBEDTLS_SUCCESS on success
 */
MbedtlsStatus_t Mbedtls_GenerateECKey( const char * pPrivateKeyPath );


MbedtlsStatus_t Mbedtls_GenerateCSR( const char * pPrivateKeyPath,
                                     char * pCsrPemBuffer,
                                     size_t csrPemBufferLength );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef MBEDTLS_POSIX_H_ */
