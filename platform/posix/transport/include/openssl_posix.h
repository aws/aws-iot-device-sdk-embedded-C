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

#ifndef OPENSSL_POSIX_H_
#define OPENSSL_POSIX_H_

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
    #define LIBRARY_LOG_NAME     "OpenSSL"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/


/**
 * @brief OpenSSL Connect / Disconnect return status.
 */
typedef enum OpensslStatus
{
    OPENSSL_SUCCESS = 0,         /**< Function successfully completed. */
    OPENSSL_INVALID_PARAMETER,   /**< At least one parameter was invalid. */
    OPENSSL_INVALID_CREDENTIALS, /**< Provided credentials were invalid. */
    OPENSSL_HANDSHAKE_FAILED,    /**< Performing TLS handshake with server failed. */
    OPENSSL_API_ERROR            /**< An error occurred when calling the OpenSSL API. */
} OpensslStatus_t;

/**
 * @brief Contains the credentials necessary to establish a TLS connection.
 */
typedef struct OpensslCredentials
{
    /**
     * @brief An array of ALPN protocols. Set to NULL to disable ALPN.
     *
     * See [this link]
     * (https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/)
     * for more information.
     */
    const char * pAlpnProtos;

    /**
     * @brief Length of the ALPN protocols array.
     */
    size_t alpnProtosLen;

    /**
     * @brief Set a host name to enable SNI. Set to NULL to disable SNI.
     */
    const char * sniHostName;

    /**
     * @brief Length of the SNI host name.
     */
    size_t sniHostNameLen;

    /**
     * @brief Set this to a non-zero value to use TLS max fragment length
     * negotiation (TLS MFLN).
     *
     * @note The network stack may have a minimum value for this parameter and
     * may return an error if this parameter is too small.
     */
    size_t maxFragmentLength;

    const char * pRootCaPath;     /**< @brief Filepath string to the trusted server root CA. */
    size_t rootCaPathLen;         /**< @brief Length associated with #NetworkCredentials.pRootCa. */
    const char * pClientCertPath; /**< @brief Filepath string to the client certificate. */
    size_t clientCertPathLen;     /**< @brief Length associated with #NetworkCredentials.pClientCert. */
    const char * pPrivateKeyPath; /**< @brief Filepath string to the client certificate's private key. */
    size_t privateKeyPathLen;     /**< @brief Length associated with #NetworkCredentials.pPrivateKey. */
} OpensslCredentials_t;

/**
 * @brief Set timeout for transport recv.
 *
 * @brief param[in] timeout The timeout to set for transport recv.
 */
void Openssl_SetRecvTimeout( int timeout );

/**
 * @brief Set timeout for transport send.
 *
 * @brief param[in] timeout The timeout to set for transport send.
 */
void Openssl_SetSendTimeout( int timeout );

/**
 * @brief Sets up a TLS session on top of a TCP connection using the OpenSSL API.
 *
 * @param[in] pNetworkContext Application-defined context (TCP socket and SSL context).
 * @param[in] pOpensslCredentials Credentials for the TLS connection.
 *
 * @return #OPENSSL_SUCCESS on success,
 * #OPENSSL_INVALID_PARAMETER, #OPENSSL_INVALID_CREDENTIALS,
 * #OPENSSL_INVALID_CREDENTIALS, #OPENSSL_SYSTEM_ERROR on failure.
 */
OpensslStatus_t Openssl_Connect( NetworkContext_t pNetworkContext,
                                 OpensslCredentials_t * pOpensslCredentials );

/**
 * @brief Closes a TLS session on top of a TCP connection using the OpenSSL API.
 *
 * @param[in] pNetworkContext Application-defined context (TCP socket and SSL context).
 *
 * @return #OPENSSL_SUCCESS on success; #OPENSSL_INVALID_PARAMETER on failure.
 */
OpensslStatus_t Openssl_Disconnect( NetworkContext_t pNetworkContext );

/**
 * @brief The transport receive function that defines the transport interface.
 *
 * This is passed as the #TransportInterface.recv function used for reading
 * data received from the network.
 *
 * @param[in] pNetworkContext Application-defined context (TCP socket and SSL context).
 * @param[out] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return Number of bytes received if successful; negative value on error.
 */
int32_t Openssl_Recv( NetworkContext_t pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv );

/**
 * @brief The transport send function that defines the transport interface.
 *
 * This is passed as the #TransportInterface.send function and used to
 * send data over the network.
 *
 * @param[in] pNetworkContext Application-defined context (TCP socket and SSL context).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Number of bytes sent if successful; negative value on error.
 */
int32_t Openssl_Send( NetworkContext_t pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend );

#endif /* ifndef OPENSSL_POSIX_H_ */
