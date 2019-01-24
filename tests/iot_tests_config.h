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

/* This file contains configuration settings for the tests. Currently, the tests
 * must run on POSIX systems. */

#ifndef _IOT_TESTS_CONFIG_H_
#define _IOT_TESTS_CONFIG_H_

/* Test framework include. */
#include "unity_fixture_malloc_overrides.h"

/* MQTT server endpoints used for the tests. */
#if AWS_IOT_TEST_MQTT_MOSQUITTO == 1
    /* Mosquitto test server. */
    #define AWS_IOT_TEST_SECURED_CONNECTION    ( 0 )
    #define AWS_IOT_TEST_SERVER                "test.mosquitto.org"
    #define AWS_IOT_TEST_PORT                  ( 1883 )
#else
    /* AWS IoT MQTT server. */
    #define AWS_IOT_TEST_SECURED_CONNECTION    ( 1 )

    /* AWS IoT endpoint and credentials. */
    #ifndef AWS_IOT_TEST_SERVER
        #define AWS_IOT_TEST_SERVER            ""
    #endif
    #ifndef AWS_IOT_TEST_PORT
        #define AWS_IOT_TEST_PORT              ( 443 )
    #endif
    #ifndef AWS_IOT_TEST_ROOT_CA
        #define AWS_IOT_TEST_ROOT_CA           ""
    #endif
    #ifndef AWS_IOT_TEST_CLIENT_CERT
        #define AWS_IOT_TEST_CLIENT_CERT       ""
    #endif
    #ifndef AWS_IOT_TEST_PRIVATE_KEY
        #define AWS_IOT_TEST_PRIVATE_KEY       ""
    #endif
#endif /* if AWS_IOT_TEST_MQTT_MOSQUITTO == 1 */

/* Shadow tests configuration. */
#ifndef AWS_IOT_TEST_SHADOW_THING_NAME
    #define AWS_IOT_TEST_SHADOW_THING_NAME     ""
#endif

/* Linear containers library configuration. */
#define IOT_CONTAINERS_ENABLE_ASSERTS               ( 1 )

/* Shadow library configuration. */
#define AWS_IOT_SHADOW_ENABLE_ASSERTS               ( 1 )

/* MQTT library configuration. */
#define AWS_IOT_MQTT_ENABLE_ASSERTS                 ( 1 )
#define AWS_IOT_MQTT_ENABLE_METRICS                 ( 0 )
#define AWS_IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES    ( 1 )
#define AWS_IOT_MQTT_TEST                           ( 1 )

/* Memory allocation function configuration. Note that these functions will not
 * be affected by AWS_IOT_STATIC_MEMORY_ONLY. */
#define AwsIotNetwork_Malloc    unity_malloc_mt
#define AwsIotNetwork_Free      unity_free_mt
#define IotThreads_Malloc       unity_malloc_mt
#define IotThreads_Free         unity_free_mt
#define AwsIotLogging_Malloc    unity_malloc_mt
#define AwsIotLogging_Free      unity_free_mt
/* #define AwsIotLogging_StaticBufferSize */
#define AwsIotTest_Malloc       unity_malloc_mt
#define AwsIotTest_Free         unity_free_mt

/* Static memory resource settings for the tests. These values must be large
 * enough to support the stress tests. */
#if AWS_IOT_STATIC_MEMORY_ONLY == 1
    #define AWS_IOT_MQTT_CONNECTIONS      ( 2 )
    #define AWS_IOT_MQTT_SUBSCRIPTIONS    ( 80 )
#endif

/* Memory allocation function configuration for libraries affected by
 * AWS_IOT_STATIC_MEMORY_ONLY. */
#if AWS_IOT_STATIC_MEMORY_ONLY == 0
    #define AwsIotMqtt_MallocConnection        unity_malloc_mt
    #define AwsIotMqtt_FreeConnection          unity_free_mt
    #define AwsIotMqtt_MallocMessage           unity_malloc_mt
    #define AwsIotMqtt_FreeMessage             unity_free_mt
    #define AwsIotMqtt_MallocOperation         unity_malloc_mt
    #define AwsIotMqtt_FreeOperation           unity_free_mt
    #define AwsIotMqtt_MallocSubscription      unity_malloc_mt
    #define AwsIotMqtt_FreeSubscription        unity_free_mt
    #define AwsIotMqtt_MallocTimerEvent        unity_malloc_mt
    #define AwsIotMqtt_FreeTimerEvent          unity_free_mt
    #define AwsIotShadow_MallocOperation       unity_malloc_mt
    #define AwsIotShadow_FreeOperation         unity_free_mt
    #define AwsIotShadow_MallocString          unity_malloc_mt
    #define AwsIotShadow_FreeString            unity_free_mt
    #define AwsIotShadow_MallocSubscription    unity_malloc_mt
    #define AwsIotShadow_FreeSubscription      unity_free_mt
#endif /* if AWS_IOT_STATIC_MEMORY_ONLY == 0 */

/* The build system will choose the appropriate system types file for the platform
 * layer based on the host operating system. */
#include IOT_SYSTEM_TYPES_FILE

#endif /* ifndef _IOT_TESTS_CONFIG_H_ */
