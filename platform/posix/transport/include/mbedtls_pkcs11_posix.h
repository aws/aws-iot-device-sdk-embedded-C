/*
 * FreeRTOS V202107.00
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

#ifndef MBEDTLS_PKCS11_POSIX_H_
#define MBEDTLS_PKCS11_POSIX_H_

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
    #define LIBRARY_LOG_NAME     "Transport_MbedTLS_PKCS11_Sockets"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_ERROR
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

/* MbedTLS includes. */
#include "mbedtls/net_sockets.h"
#include "mbedtls/ssl.h"
#include "mbedtls/pk.h"
#include "mbedtls/pk_internal.h"

/* Transport interface include. */
#include "transport_interface.h"

/* PKCS #11 includes. */
#include "core_pkcs11.h"

/**
 * @brief Definition of the network context for the transport interface
 * implementation that uses mbedTLS and FreeRTOS+TLS sockets.
 */
typedef struct MbedtlsPkcs11Context
{
    mbedtls_net_context socketContext;    /**< @brief MbedTLS socket context. */
    mbedtls_ssl_config config;            /**< @brief SSL connection configuration. */
    mbedtls_ssl_context context;          /**< @brief SSL connection context */
    mbedtls_x509_crt_profile certProfile; /**< @brief Certificate security profile for this connection. */
    mbedtls_x509_crt rootCa;              /**< @brief Root CA certificate context. */
    mbedtls_x509_crt clientCert;          /**< @brief Client certificate context. */
    mbedtls_pk_context privKey;           /**< @brief Client private key context. */
    mbedtls_pk_info_t privKeyInfo;        /**< @brief Client private key info. */

    /* PKCS #11. */
    CK_FUNCTION_LIST_PTR pP11FunctionList;
    CK_SESSION_HANDLE p11Session;
    CK_OBJECT_HANDLE p11PrivateKey;
    CK_KEY_TYPE keyType;
} MbedtlsPkcs11Context_t;

/**
 * @brief TLS Connect / Disconnect return status.
 */
typedef enum MbedtlsPkcs11Status
{
    MBEDTLS_PKCS11_SUCCESS = 0,         /**< Function successfully completed. */
    MBEDTLS_PKCS11_INVALID_PARAMETER,   /**< At least one parameter was invalid. */
    MBEDTLS_PKCS11_INSUFFICIENT_MEMORY, /**< Insufficient memory required to establish connection. */
    MBEDTLS_PKCS11_INVALID_CREDENTIALS, /**< Provided credentials were invalid. */
    MBEDTLS_PKCS11_HANDSHAKE_FAILED,    /**< Performing TLS handshake with server failed. */
    MBEDTLS_PKCS11_INTERNAL_ERROR,      /**< A call to a system API resulted in an internal error. */
    MBEDTLS_PKCS11_CONNECT_FAILURE      /**< Initial connection to the server failed. */
} MbedtlsPkcs11Status_t;

/**
 * @brief Contains the credentials necessary for tls connection setup.
 */
typedef struct MbedtlsPkcs11Credentials
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
    char * pClientCertLabel;      /**< @brief String representing the PKCS #11 label for the client certificate. */
    char * pPrivateKeyLabel;      /**< @brief String representing the PKCS #11 label for the private key. */
    CK_SESSION_HANDLE p11Session; /**< @brief PKCS #11 session handle. */
} MbedtlsPkcs11Credentials_t;

/**
 * @brief Sets up a TLS session on top of a TCP connection using the MbedTLS API.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 * @param[in] pHostName The hostname of the remote endpoint.
 * @param[in] port The destination port.
 * @param[in] pMbedtlsPkcs11Credentials Credentials for the TLS connection.
 *
 * @note A timeout of 0 means infinite timeout.
 *
 * @return #MBEDTLS_PKCS11_SUCCESS on success;
 * #MBEDTLS_PKCS11_INSUFFICIENT_MEMORY, #MBEDTLS_PKCS11_INVALID_CREDENTIALS,
 * #MBEDTLS_PKCS11_HANDSHAKE_FAILED, #MBEDTLS_PKCS11_INTERNAL_ERROR,
 * or #MBEDTLS_PKCS11_CONNECT_FAILURE on failure.
 */
MbedtlsPkcs11Status_t Mbedtls_Pkcs11_Connect( NetworkContext_t * pNetworkContext,
                                              const char * pHostName,
                                              uint16_t port,
                                              const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials );

/**
 * @brief Gracefully disconnect an established TLS connection.
 *
 * @param[in] pNetworkContext Network context.
 */
void Mbedtls_Pkcs11_Disconnect( NetworkContext_t * pNetworkContext );

/**
 * @brief Receives data over an established TLS session using the MbedTLS API.
 *
 * This can be used as #TransportInterface.recv function for receiving data
 * from the network.
 *
 * @param[in] pNetworkContext The network context created using Mbedtls_Pkcs11_Connect API.
 * @param[out] pBuffer Buffer to receive network data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return Number of bytes received if successful; negative value to indicate failure.
 * A return value of zero represents that the receive operation can be retried.
 */
int32_t Mbedtls_Pkcs11_Recv( NetworkContext_t * pNetworkContext,
                             void * pBuffer,
                             size_t bytesToRecv );

/**
 * @brief Sends data over an established TLS session using the MbedTLS API.
 *
 * This can be used as the #TransportInterface.send function to send data
 * over the network.
 *
 * @param[in] pNetworkContext The network context created using Mbedtls_Pkcs11_Connect API.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Number of bytes sent if successful; negative value on error.
 *
 * @note This function does not return zero value because it cannot be retried
 * on send operation failure.
 */
int32_t Mbedtls_Pkcs11_Send( NetworkContext_t * pNetworkContext,
                             const void * pBuffer,
                             size_t bytesToSend );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef MBEDTLS_PKCS11_POSIX_H_ */
