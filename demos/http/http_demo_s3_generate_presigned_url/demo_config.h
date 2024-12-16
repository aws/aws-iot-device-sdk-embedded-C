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
 * @brief Path of the file containing the server's root CA certificate.
 *
 * This certificate is used to identify the AWS endpoints and is publicly
 * available. Refer to the AWS documentation available in the link below
 * https://docs.aws.amazon.com/iot/latest/developerguide/server-authentication.html#server-authentication-certs
 *
 * Amazon's root CA certificate is automatically downloaded to the certificates
 * directory from @ref https://www.amazontrust.com/repository/AmazonRootCA1.pem
 * using the CMake build system.
 *
 * @note This certificate should be PEM-encoded.
 * @note This path is relative from the demo binary created. Update
 * ROOT_CA_CERT_PATH to the absolute path if this demo is executed from elsewhere.
 */
#ifndef ROOT_CA_CERT_PATH
    #define ROOT_CA_CERT_PATH    "certificates/AmazonRootCA1.crt"
#endif

/**
 * @brief Path of the file containing the server's root CA certificate for S3
 * authentication.
 *
 * This certificate is used to identify the AWS S3 server and is publicly
 * available. Refer to the AWS documentation available in the link below
 * https://docs.aws.amazon.com/iot/latest/developerguide/server-authentication.html#server-authentication-certs
 *
 * Amazon's root CA certificate is automatically downloaded to the certificates
 * directory from @ref https://www.amazontrust.com/repository/AmazonRootCA1.pem
 * using the CMake build system.
 *
 * @note This certificate should be PEM-encoded.
 */
#ifndef ROOT_CA_CERT_PATH_S3
    #define ROOT_CA_CERT_PATH_S3    ROOT_CA_CERT_PATH
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
#ifndef AWS_IOT_THING_NAME
    #define AWS_IOT_THING_NAME    "...insert here..."
#endif

/**
 * @brief Endpoint for the AWS IOT credential provider.
 *
 * @note Can be found with
 * `aws iot describe-endpoint --endpoint-type iot:CredentialProvider` from
 * the AWS CLI.
 */
#ifndef AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT
    #define AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT    "...insert here..."
#endif

/**
 * @brief Role alias name for accessing the credential provider.
 * 
 * @note This is the name of the role alias created in AWS IoT
 * while setting up AWS resources before running the demo.
 * Refer to the demo setup instructions in the README.md file
 * within the same directory as this file in the repository.
 */
#ifndef AWS_IOT_CREDENTIAL_PROVIDER_ROLE
    #define AWS_IOT_CREDENTIAL_PROVIDER_ROLE    "...insert here..."
#endif

/**
 * @brief Name of bucket in AWS S3 from where file needs to be downloaded.
 */
#ifndef AWS_S3_BUCKET_NAME
    #define AWS_S3_BUCKET_NAME    "...insert here..."
#endif

/**
 * @brief AWS Region where the bucket resides.
 */
#ifndef AWS_S3_BUCKET_REGION
    #define AWS_S3_BUCKET_REGION    "...insert here..."
#endif

/**
 * @brief Name of file that needs to be downloaded from AWS S3.
 */
#ifndef AWS_S3_OBJECT_NAME
    #define AWS_S3_OBJECT_NAME    "...insert here..."
#endif

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 *
 * @note A portion of the user buffer will be used to store the response header,
 * so the length of the response body returned on any given range request will
 * be less than USER_BUFFER_LENGTH. We don't expect S3 to send more than 1024
 * bytes of headers.
 */
#define USER_BUFFER_LENGTH                ( 4096 )

#endif /* ifndef DEMO_CONFIG_H_ */
