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

#ifndef DEMO_CONFIG_H
#define DEMO_CONFIG_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Include logging header files and define logging macros in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for DEMO.
 * 3. Include the header file "logging_stack.h", if logging is enabled for DEMO.
 */

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
 * @brief MQTT server host name.
 *
 * This demo can be run using the open-source Mosquitto broker tool.
 * A Mosquitto MQTT broker can be setup locally for running this demo against
 * it. Please refer to the instructions in https://mosquitto.org/ for running
 * a Mosquitto broker locally.
 * Alternatively,instructions to run Mosquitto server on Docker container can
 * be viewed in the README.md of the root directory.
 *
 * #define BROKER_ENDPOINT               "...insert here..."
 */

/**
 * @brief MQTT server port number.
 *
 * In general, port 8883 is for secured MQTT connections.
 */
#define BROKER_PORT    ( 8883 )

/**
 * @brief Path of the file containing the server's root CA certificate.
 *
 * This certificate should be PEM-encoded.
 *
 * #define ROOT_CA_CERT_PATH               "....insert here...."
 */

/**
 * @brief MQTT client identifier.
 *
 * No two clients may use the same client identifier simultaneously.
 */
#ifndef CLIENT_IDENTIFIER
    #define CLIENT_IDENTIFIER    "testclient1"
#endif

/**
 * @brief The max size of the registry in the subscription manager.
 *
 * The registry of the subscription manager component of the demo represents
 * a list of pairs of topic filter and its subscription callback. The
 * subscription callback is invoked when an incoming PUBLISH message is received
 * on a matching topic in the demo.
 * The memory of the registry is statically allocated whose size is dependent
 * on the value of this macro.
 *
 * As this demo uses 3 topic filters, the minimum value of this config should be
 * 3 for a successful execution of the demo.
 */
#define MAX_SUBSCRIPTION_CALLBACK_RECORDS    5

#endif /* ifndef DEMO_CONFIG_H */
