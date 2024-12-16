/*
 * AWS IoT Device SDK for Embedded C 202412.00
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

#ifndef HTTP_DEMO_S3_UTILS_H_
#define HTTP_DEMO_S3_UTILS_H_

/* Standard includes. */
#include <stdlib.h>
#include <stdbool.h>

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Other HTTP utils header. */
#include "http_demo_utils.h"

/* JSON API header. */
#include "core_json.h"

/* SIGV4 API header. */
#include "sigv4.h"

/**
 * @brief Length in bytes of hex encoded hash digest.
 */
#define HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH    ( ( ( uint16_t ) 64 ) )

/**
 * @brief Length in bytes of SHA256 hash digest.
 */
#define SHA256_HASH_DIGEST_LENGTH                ( HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH / 2 )

/**
 * @brief Maximum Length for AWS IOT Credential provider server host name.
 *
 * @note length of the AWS IOT Credential provider server host name string
 * cannot exceed this value.
 */
#define SERVER_HOST_NAME_MAX_LENGTH              65U

/**
 * @brief The host address string extracted from the AWS IOT CREDENTIAL PROVIDER URL.
 *
 * @note SERVER_HOST_NAME_MAX_LENGTH is set as the array length here as the
 * length of the host name string cannot exceed this value.
 */
extern char serverHost[ SERVER_HOST_NAME_MAX_LENGTH ];

/**
 * @brief The length of the host address found in the the AWS IOT CREDENTIAL PROVIDER URL.
 */
extern size_t serverHostLength;

/**
 * @brief The security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
extern const char * pSecurityToken;

/**
 * @brief Length of security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
extern size_t securityTokenLen;

/**
 * @brief The expiration time for the temporary credentials retrieved
 * from AWS IoT credential provider service.
 */
extern const char * pExpiration;

/**
 * @brief Retrieve the temporary credentials from AWS IOT Credential Provider.
 *
 * @param[in] pTransportInterface The transport interface for performing network send/recv operations.
 * @param[out] pDateISO8601 Buffer to store the ISO8601 formatted date.
 * @param[in] pDateISO8601Len Length of the buffer provided to store ISO8601 formatted date.
 * @param[in,out] response Response buffer to store the HTTP response received.
 * @param[out] sigvCreds Buffer to store the parsed credentials.
 *
 * @return `true` if credentials are retrieved successfully otherwise 'false`.
 */
bool getTemporaryCredentials( TransportInterface_t * transportInterface,
                              char * pDateISO8601,
                              size_t pDateISO8601Len,
                              HTTPResponse_t * response,
                              SigV4Credentials_t * sigvCreds );

/**
 * @brief Calculate SHA256 digest.
 *
 * @param[in] pInput Input string to hash.
 * @param[in] ilen Length of input string.
 * @param[out] pOutput Buffer to store the generated hash.
 */
int32_t sha256( const char * pInput,
                size_t ilen,
                char * pOutput );

/**
 * @brief Application-defined Hash Initialization function provided
 * to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
int32_t sha256Init( void * hashContext );

/**
 * @brief Application-defined Hash Update function provided to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
int32_t sha256Update( void * hashContext,
                      const uint8_t * pInput,
                      size_t inputLen );

/**
 * @brief Application-defined Hash Final function provided to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
int32_t sha256Final( void * hashContext,
                     uint8_t * pOutput,
                     size_t outputLen );

/**
 * @brief Connect to AWS IOT Credential Provider server with reconnection retries.
 *
 * @param[out] pNetworkContext The output parameter to return the created
 * network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
int32_t connectToIotServer( NetworkContext_t * pNetworkContext );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef HTTP_DEMO_S3_UTILS_H_ */
