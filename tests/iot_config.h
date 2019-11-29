/*
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* This file contains configuration settings for the tests. */

#ifndef IOT_CONFIG_H_
#define IOT_CONFIG_H_

/* The build system will choose the appropriate system types file for the platform
 * layer based on the host operating system. */
#include IOT_SYSTEM_TYPES_FILE

/* Test framework include. */
#include "unity_fixture_malloc_overrides.h"

/* MQTT server endpoints used for the tests. */
#if IOT_TEST_MQTT_MOSQUITTO == 1
    /* Mosquitto test server. */
    #define IOT_TEST_SECURED_CONNECTION    ( 0 )

    #ifndef IOT_TEST_SERVER
        #define IOT_TEST_SERVER            "test.mosquitto.org"
    #endif
    #ifndef IOT_TEST_PORT
        #define IOT_TEST_PORT              ( 1883 )
    #endif
#else
    /* AWS IoT MQTT server. */
    #define IOT_TEST_SECURED_CONNECTION    ( 1 )

/* AWS IoT endpoint and credentials. */
    #ifndef IOT_TEST_SERVER
        #define IOT_TEST_SERVER         ""
    #endif
    #ifndef IOT_TEST_PORT
        #define IOT_TEST_PORT           ( 443 )
    #endif
    #ifndef IOT_TEST_ROOT_CA
        #define IOT_TEST_ROOT_CA        ""
    #endif
    #ifndef IOT_TEST_CLIENT_CERT
        #define IOT_TEST_CLIENT_CERT    ""
    #endif
    #ifndef IOT_TEST_PRIVATE_KEY
        #define IOT_TEST_PRIVATE_KEY    ""
    #endif
    #ifndef IOT_TEST_USER_NAME
        #define IOT_TEST_USER_NAME      ""
    #endif
    #ifndef IOT_TEST_PASSWORD
        #define IOT_TEST_PASSWORD       ""
    #endif
#endif /* if IOT_TEST_MQTT_MOSQUITTO == 1 */

/* Shadow tests configuration. */
#ifndef AWS_IOT_TEST_SHADOW_THING_NAME
    #define AWS_IOT_TEST_SHADOW_THING_NAME    ""
#endif

/* Jobs tests configuration. */
#ifndef AWS_IOT_TEST_JOBS_THING_NAME
    #define AWS_IOT_TEST_JOBS_THING_NAME    ""
#endif

/* Defender tests configuration. */
#ifndef AWS_IOT_TEST_DEFENDER_THING_NAME
    #define AWS_IOT_TEST_DEFENDER_THING_NAME    ""
#endif

/* Provisioning tests configuration */
#ifndef AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME
    #define AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME    ""
#endif
#ifndef AWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS
    #define AWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS       \
    {                                                           \
        {                                                       \
            .pParameterKey = "SerialNumber",                    \
            .parameterKeyLength = sizeof( "SerialNumber" ) - 1, \
            .pParameterValue = "",                              \
            .parameterValueLength = 0                           \
        }                                                       \
    }
#endif /* ifndef AWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS */

/* Log level for testing the demos. */
#define IOT_LOG_LEVEL_DEMO    IOT_LOG_INFO

/* Set the equivalent demo defines. */
#ifdef IOT_TEST_SECURED_CONNECTION
    #define IOT_DEMO_SECURED_CONNECTION    IOT_TEST_SECURED_CONNECTION
#endif
#ifdef IOT_TEST_SERVER
    #define IOT_DEMO_SERVER                IOT_TEST_SERVER
#endif
#ifdef IOT_TEST_PORT
    #define IOT_DEMO_PORT                  IOT_TEST_PORT
#endif
#ifdef IOT_TEST_ROOT_CA
    #define IOT_DEMO_ROOT_CA               IOT_TEST_ROOT_CA
#endif
#ifdef IOT_TEST_CLIENT_CERT
    #define IOT_DEMO_CLIENT_CERT           IOT_TEST_CLIENT_CERT
#endif
#ifdef IOT_TEST_PRIVATE_KEY
    #define IOT_DEMO_PRIVATE_KEY           IOT_TEST_PRIVATE_KEY
#endif
#ifdef IOT_TEST_USER_NAME
    #define IOT_DEMO_USER_NAME             IOT_TEST_USER_NAME
#endif
#ifdef IOT_TEST_PASSWORD
    #define IOT_DEMO_PASSWORD              IOT_TEST_PASSWORD
#endif
#if defined( IOT_TEST_MQTT_CLIENT_IDENTIFIER )
    #define IOT_DEMO_IDENTIFIER            IOT_TEST_MQTT_CLIENT_IDENTIFIER
#elif defined( AWS_IOT_TEST_SHADOW_THING_NAME )
    #define IOT_DEMO_IDENTIFIER            AWS_IOT_TEST_SHADOW_THING_NAME
#endif

/* Set defines required for Provisioning demo when building demo target with IOT_BUILD_TESTS set to 1. */
#ifdef AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME
    #define AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME                           AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME            "SerialNumber"
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME_LENGTH
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME_LENGTH     sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME ) - 1
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE           ""
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE_LENGTH
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE_LENGTH    sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE ) - 1
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME                        ""
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME_LENGTH
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME_LENGTH                 sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME ) - 1
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE                       ""
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE_LENGTH
    #define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE_LENGTH                sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE ) - 1
#endif

/* Enable asserts in the libraries. */
#define IOT_CONTAINERS_ENABLE_ASSERTS           ( 1 )
#define IOT_MQTT_ENABLE_ASSERTS                 ( 1 )
#define IOT_TASKPOOL_ENABLE_ASSERTS             ( 1 )
#define IOT_SERIALIZER_ENABLE_ASSERTS           ( 1 )
#define AWS_IOT_SHADOW_ENABLE_ASSERTS           ( 1 )
#define AWS_IOT_DEFENDER_ENABLE_ASSERTS         ( 1 )
#define AWS_IOT_JOBS_ENABLE_ASSERTS             ( 1 )
#define AWS_IOT_PROVISIONING_ENABLE_ASSERTS     ( 1 )

/* MQTT library configuration. */
#define IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES    ( 1 )

/* Defender library configuration. */
#define AWS_IOT_DEFENDER_USE_LONG_TAG           ( 1 )

/* Allow the use of multiple Jobs callbacks. */
#define AWS_IOT_JOBS_NOTIFY_CALLBACKS           ( 4 )

/* Static memory resource settings for the tests. These values must be large
 * enough to support the stress tests. */
#if IOT_STATIC_MEMORY_ONLY == 1
    #define IOT_MESSAGE_BUFFERS                    ( 16 )
    #define IOT_MQTT_CONNECTIONS                   ( 2 )
    #define IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS    ( 10 )
    #define IOT_MQTT_SUBSCRIPTIONS                 ( 80 )
    #define IOT_TASKPOOLS                          ( 4 )
#endif

/* Default assert function. */
#include <assert.h>
#define Iot_DefaultAssert    assert

/* Memory allocation function configuration. Note that these functions will not
 * be affected by IOT_STATIC_MEMORY_ONLY. */
#define IotThreads_Malloc    unity_malloc_mt
#define IotThreads_Free      unity_free_mt
#define IotNetwork_Malloc    unity_malloc_mt
#define IotNetwork_Free      unity_free_mt
#define IotLogging_Malloc    unity_malloc_mt
#define IotLogging_Free      unity_free_mt
/* #define IotLogging_StaticBufferSize */
#define IotTest_Malloc       unity_malloc_mt
#define IotTest_Free         unity_free_mt

/* Memory allocation function configuration for libraries affected by
 * IOT_STATIC_MEMORY_ONLY. */
#if IOT_STATIC_MEMORY_ONLY == 0
    #define Iot_DefaultMalloc    unity_malloc_mt
    #define Iot_DefaultFree      unity_free_mt
#endif /* if IOT_STATIC_MEMORY_ONLY == 0 */

/* Choose the appropriate network abstraction implementation. */
#if IOT_NETWORK_USE_OPENSSL == 1
    /* OpenSSL network include. */
    #define IOT_TEST_NETWORK_HEADER       "iot_network_openssl.h"

    #define IOT_TEST_ALPN_PROTOS          "\x0ex-amzn-mqtt-ca"
    #define IOT_TEST_NETWORK_INTERFACE    IOT_NETWORK_INTERFACE_OPENSSL

    #define IotTestNetwork_Init           IotNetworkOpenssl_Init
    #define IotTestNetwork_Cleanup        IotNetworkOpenssl_Cleanup
#else
    /* mbed TLS network include. */
    #define IOT_TEST_NETWORK_HEADER       "iot_network_mbedtls.h"

    #define IOT_TEST_ALPN_PROTOS          "x-amzn-mqtt-ca"
    #define IOT_TEST_NETWORK_INTERFACE    IOT_NETWORK_INTERFACE_MBEDTLS

    #define IotTestNetwork_Init           IotNetworkMbedtls_Init
    #define IotTestNetwork_Cleanup        IotNetworkMbedtls_Cleanup
#endif /* if IOT_NETWORK_USE_OPENSSL == 1 */

/* Initializers for the tests' network types. */
#define IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER \
    {                                            \
        .pHostName = IOT_TEST_SERVER,            \
        .port = IOT_TEST_PORT                    \
    }

#if IOT_TEST_SECURED_CONNECTION == 1
    #define IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER \
    {                                                \
        .pAlpnProtos = IOT_TEST_ALPN_PROTOS,         \
        .pRootCa = IOT_TEST_ROOT_CA,                 \
        .pClientCert = IOT_TEST_CLIENT_CERT,         \
        .pPrivateKey = IOT_TEST_PRIVATE_KEY,         \
        .pUserName = IOT_TEST_USER_NAME,             \
        .pPassword = IOT_TEST_PASSWORD               \
    }
#else
    #define IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER    { 0 }
#endif /* if IOT_TEST_SECURED_CONNECTION == 1 */

/* Configure code coverage testing if enabled. */
#if IOT_TEST_COVERAGE == 1
    #ifndef __GNUC__
        #error "Unsupported compiler. Only gcc and clang are supported for coverage."
    #endif

/* Define the empty else marker if test coverage is enabled. */
    #define EMPTY_ELSE_MARKER    __asm__ __volatile__ ( "nop" )

/* Define a custom logging puts function. This function allows coverage
 * testing of logging functions, but prevents excessive logs from being
 * printed. */
    #define IotLogging_Puts      _coveragePuts

/* Includes for coverage logging puts. */
    #include <stdbool.h>
    #include <stdio.h>
    #include <string.h>

/* Logging output function that only prints messages from demo executables.
 * May be unused, hence the gcc unused attribute (not portable!) */
    static int __attribute__( ( unused ) ) _coveragePuts( const char * pMessage )
    {
        bool printMessage = false;

        /* Name of this executable, available through glibc (not portable!) */
        extern const char * __progname;

        /* Check if this is a demo executable. */
        if( strstr( __progname, "demo" ) != NULL )
        {
            /* Always print messages from the demo executables. */
            if( strstr( pMessage, "[DEMO]" ) != NULL )
            {
                printMessage = true;
            }
            /* Always print errors in demo executables. */
            else if( strstr( pMessage, "[ERROR]" ) != NULL )
            {
                printMessage = true;
            }
            /* Always print warnings in demo executables. */
            else if( strstr( pMessage, "[WARN ]" ) != NULL )
            {
                printMessage = true;
            }
        }

        if( printMessage == true )
        {
            puts( pMessage );
        }

        /* Puts should return a nonzero value. */
        return 1;
    }
#endif /* if IOT_TEST_COVERAGE == 1 */

#endif /* ifndef IOT_CONFIG_H_ */
