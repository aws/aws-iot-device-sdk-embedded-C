/*
 * AWS IoT Device SDK for Embedded C 202108.00
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

#ifndef DEMO_CONFIG_H_
#define DEMO_CONFIG_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging config definition and header files inclusion are required in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for DEMO.
 * 3. Include the header file "logging_stack.h", if logging is enabled for DEMO.
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "DEMO"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief HTTP server port number.
 *
 * In general, port 443 is for TLS HTTP connections.
 */
#ifndef HTTPS_PORT
    #define HTTPS_PORT    443
#endif

/**
 * @brief Path of the file containing the AWS IOT Credential provider
 * server's root CA certificate for TLS authentication.
 *
 * @note This certificate should be PEM-encoded.
 */
#ifndef AWS_IOT_CRED_PROVIDER_ROOT_CA_CERT_PATH
    #define AWS_IOT_CRED_PROVIDER_ROOT_CA_CERT_PATH    "certificates/AmazonRootCA1.crt"
#endif

/**
 * @brief Path of the file containing the AWS S3 server's root CA certificate for TLS
 * authentication.
 *
 * The Baltimore Cybertrust Root CA Certificate is automatically downloaded to
 * the certificates directory using the CMake build system, from @ref
 * https://cacerts.digicert.com/BaltimoreCyberTrustRoot.crt.pem.
 *
 * @note This certificate should be PEM-encoded.
 */
#ifndef AWS_S3_ROOT_CA_CERT_PATH
    #define AWS_S3_ROOT_CA_CERT_PATH    "certificates/BaltimoreCyberTrustRoot.crt"
#endif

/**
 * @brief Path of the file containing the client certificate for TLS
 * authentication with AWS IOT credential provider.
 *
 * @note This certificate should be PEM-encoded.
 */
#ifndef CLIENT_CERT_PATH
    #define CLIENT_CERT_PATH    "...insert here..."
#endif

/**
 * @brief Path of the file containing the client private key for TLS
 * authentication with AWS IOT credential provider.
 *
 * @note This key should be PEM-encoded.
 */
#ifndef CLIENT_PRIVATE_KEY_PATH
    #define CLIENT_PRIVATE_KEY_PATH    "...insert here..."
#endif

/**
 * @brief Define AWS IOT thing name.
 */
#define AWS_IOT_THING_NAME                      "...insert here..."

/**
 * @brief Endpoint for the AWS IOT credential provider.
 *
 * @note Can be found with
 * `aws iot describe-endpoint --endpoint-type iot:CredentialProvider` from
 * the AWS CLI.
 */
#define AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT    "...insert here..."

/**
 * @brief Role alias name for accessing the credential provider.
 * 
 * @note This is the name of the role alias created in AWS IoT
 * while setting up AWS resources before running the demo.
 * Refer to the demo setup instructions in the README.md file
 * within the same directory as this file in the repository.
 */
#define AWS_IOT_CREDENTIAL_PROVIDER_ROLE        "...insert here..."

/**
 * @brief Name of bucket in AWS S3 from where file needs to be downloaded.
 */
#define AWS_S3_BUCKET_NAME                      "...insert here..."

/**
 * @brief AWS Region where the bucket resides.
 */
#define AWS_S3_BUCKET_REGION                    "...insert here..."

/**
 * @brief Name of file that needs to be downloaded from AWS S3.
 */
#define AWS_S3_OBJECT_NAME                      "...insert here..."

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS          ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 *
 * @note A portion of the user buffer will be used to store the response header,
 * so the length of the response body returned on any given range request will
 * be less than USER_BUFFER_LENGTH. We don't expect S3 to send more than 1024
 * bytes of headers.
 */
#define USER_BUFFER_LENGTH                      ( 4096 )

/**
 * @brief The size of the range of the file to download, with each request.
 *
 * @note This should account for the response headers that will also be stored
 * in the user buffer. We don't expect S3 to send more than 1024 bytes of
 * headers.
 */
#define RANGE_REQUEST_LENGTH                    ( 2048 )

#endif /* ifndef DEMO_CONFIG_H_ */
