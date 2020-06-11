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

#ifndef DEMO_CONFIG_H_
#define DEMO_CONFIG_H_

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
 * @brief HTTP server host name.
 */
#define SERVER_HOST                       "placeholder.iot.us-west-2.amazonaws.com"

/**
 * @brief HTTP server port number.
 *
 * @note Port 443 is normally used for HTTPS connections. However, because 443
 * is reserved for MQTT in AWS IoT Core, port 8443 is used instead.
 */
#define SERVER_PORT                       8443

/**
 * @brief Path of the file containing the server's root CA certificate for TLS authentication.
 *
 * @note This certificate should be PEM-encoded.
 */
#define SERVER_CERT_PATH                  "certificates/AmazonRootCA1.crt"

/**
 * @brief Path of the file containing the client's certificate for TLS authentication.
 *
 * For the purposes of this demo, a self-signed certificate is used. However,
 * in production, this certificate should be signed by a certifying authority
 * that is trusted by the server.
 *
 * @note This certificate should be PEM-encoded.
 */
#define CLIENT_CERT_PATH                  "certificates/client.crt"

/**
 * @brief Path of the file containing the client's key for TLS client authentication.
 *
 *
 * @note This key should be PEM-encoded.
 */
#define CLIENT_KEY_PATH                   "certificates/client.key"

/**
 * @brief HTTP server path to perform the mutually authenticated request.
 * This will publish a "Hello World" message to a topic named topic.
 *
 * @note QoS=1 implies the message is delivered at least once.
 */
#define POST_PATH                         "/topics/topic?qos=1"

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define USER_BUFFER_LENGTH                ( 4096 )

/**
 * @brief Request body to send for PUT and POST requests in this demo.
 */
#define REQUEST_BODY                      "{ \"message\": \"Hello, world\" }"

#endif /* ifndef DEMO_CONFIG_H */
