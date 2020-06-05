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

#ifndef DEMO_CONFIG_H
#define DEMO_CONFIG_H

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
#define LIBRARY_LOG_NAME     "DEMO"
#define LIBRARY_LOG_LEVEL    LOG_INFO

#include "logging_stack.h"

/************ End of logging configuration ****************/


/**
 * @brief MQTT server host name.
 *
 * This demo uses the AWS IoT broker end point test server.
 */
#define BROKER_ENDPOINT            "a3c4bx1snc0lp8-ats.iot.us-west-2.amazonaws.com"

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH     ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief Path of the file containing the server's root CA certificate.
 *
 * This certificate should be PEM-encoded.
 */
#define SERVER_CERT_PATH           "certificates/root_ca_cert"

/**
 * @brief Length of path to server certificate.
 */
#define SERVER_CERT_PATH_LENGTH    ( ( uint16_t ) ( sizeof( SERVER_CERT_PATH ) - 1 ) )

/**
 * @brief Path of the file containing the client certificate.
 *
 * This certificate should be PEM-encoded.
 */
#define CLIENT_CERT_PATH           "certificates/MyIOTThingTest5_cert_pem_file"

/**
 * @brief Length of path to client certificate.
 */
#define CLIENT_CERT_PATH_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_CERT_PATH ) - 1 ) )

/**
 * @brief Path of the file containing the client's private key.
 *
 * This private should be PEM-encoded.
 */
#define CLIENT_PRIVATE_KEY_PATH           "certificates/MyIOTThingTest5_private_key_pem_file"

/**
 * @brief Length of path to client's private key.
 */
#define CLIENT_PRIVATE_KEY_PATH_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_PRIVATE_KEY_PATH ) - 1 ) )

/**
 * @brief MQTT client identifier.
 *
 * No two clients may use the same client identifier simultaneously.
 */
#define CLIENT_IDENTIFIER    "MyIOTThingTest5"

#endif /* ifndef DEMO_CONFIG_H */
