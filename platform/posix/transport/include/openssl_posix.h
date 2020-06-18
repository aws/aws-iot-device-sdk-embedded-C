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

#ifndef OPENSSL_CONFIG_H_
#define OPENSSL_CONFIG_H_

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
 * @brief Contains the credentials necessary for TLS connection establishment.
 */
typedef struct NetworkCredentials
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
    size_t alpnProtosLen;

    /**
     * @brief Set this to a non-zero value to use TLS max fragment length
     * negotiation (TLS MFLN).
     *
     * @note The network stack may have a minimum value for this parameter and
     * may return an error if this parameter is too small.
     */
    size_t maxFragmentLength;

    /**
     * @brief Flags to configure the TLS connection.
     */
    uint16_t flags;

    const char * pRootCaPath;     /**< @brief Filepath string to the trusted server root certificate. */
    size_t rootCaPathLen;         /**< @brief Length associated with #NetworkCredentials.pRootCa. */
    const char * pClientCertPath; /**< @brief Filepath string to the client certificate. */
    size_t clientCertPathLen;     /**< @brief Length associated with #NetworkCredentials.pClientCert. */
    const char * pPrivateKeyPath; /**< @brief Filepath string to the client certificate's private key. */
    size_t privateKeyPathLen;     /**< @brief Length associated with #NetworkCredentials.pPrivateKey. */
} NetworkCredentials_t;

NetworkStatus_t Openssl_Establish( NetworkContext_t pNetworkContext,
                                   NetworkCredentials_t * pNetworkCredentials );

NetworkStatus_t OpenSSL_Terminate( NetworkContext_t pNetworkContext );

int32_t OpenSSL_Recv( NetworkContext_t pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv );

int32_t OpenSSL_Send( NetworkContext_t pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend );

#endif /* ifndef OPENSSL_CONFIG_H_ */
