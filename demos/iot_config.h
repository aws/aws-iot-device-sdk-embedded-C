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

/* This file contains configuration settings for the demos. */

#ifndef IOT_CONFIG_H_
#define IOT_CONFIG_H_

/* Server endpoints used for the demos. May be overridden with command line
 * options at runtime. */
#define IOT_DEMO_SECURED_CONNECTION    ( true ) /* Command line: -s (secured) or -u (unsecured) */
#define IOT_DEMO_SERVER                ""       /* Command line: -h */
#define IOT_DEMO_PORT                  ( 443 )  /* Command line: -p */

/* Credential paths. May be overridden with command line options at runtime. */
#define IOT_DEMO_ROOT_CA               "" /* Command line: -r */
#define IOT_DEMO_CLIENT_CERT           "" /* Command line: -c */
#define IOT_DEMO_PRIVATE_KEY           "" /* Command line: -k */
#define IOT_DEMO_USER_NAME             "" /* Command line: -m */
#define IOT_DEMO_PASSWORD              "" /* Command line: -w */

/* MQTT client identifier (MQTT demo only) or AWS IoT Thing Name. May be set at
 * runtime with the command line option -i. Identifiers are optional for the
 * MQTT demo, but required for demos requiring a Thing Name. (The MQTT demo will
 * generate a unique identifier if no identifier is given). */
/* #define IOT_DEMO_IDENTIFIER         "" */

/* MQTT demo configuration. The demo publishes bursts of messages. */
#define IOT_DEMO_MQTT_PUBLISH_BURST_COUNT          ( 10 )                 /* Number of message bursts. */
#define IOT_DEMO_MQTT_PUBLISH_BURST_SIZE           ( 10 )                 /* Number of messages published in each burst.
                                                                           * */

/* Shadow demo configuration. The demo publishes periodic Shadow updates and responds
 * to changing Shadows. */
#define AWS_IOT_DEMO_SHADOW_UPDATE_COUNT           ( 20 )                   /* Number of updates to publish. */
#define AWS_IOT_DEMO_SHADOW_UPDATE_PERIOD_MS       ( 3000 )                 /* Period of Shadow updates. */

/**
 * The name for the provisioning template that will be used for provisioning the demo app.
 */
#define AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME    ""

/**
 * List of parameters that will be used for provisioning in the demo application.
 * There are 2 requirements for passing parameters to the Provisioning demo:
 * 1. One parameter is a "SerialNumber". The AWS IoT console generates a provisioning template
 * that by default uses a "SerialNumber" device parameter for creating a Thing resource. Also, the
 * demo setup instructions (on <PLACEHOLDER FOR LINK>) provide an AWS CLI command example for creating
 * a provisioning template, in which the template JSON string contains the "SerialNumber" parameter.
 * 2. A second parameter which is configurable for both the name and value. The example provisioning
 * JSON string in the demo setup instructions contains "DeviceLocation" as the default parameter name.
 * If a different parameter name is used, make SURE to update the provisioning template on the AWS IoT Console!
 */

#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME            "SerialNumber"
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME_LENGTH     sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME ) - 1
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE           ""
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE_LENGTH    sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE ) - 1
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME                        ""
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME_LENGTH                 sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME ) - 1
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE                       ""
#define AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE_LENGTH                sizeof( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE ) - 1

/* Enable asserts in the libraries. */
#define IOT_CONTAINERS_ENABLE_ASSERTS                                     ( 1 )
#define IOT_MQTT_ENABLE_ASSERTS                                           ( 1 )
#define IOT_TASKPOOL_ENABLE_ASSERTS                                       ( 1 )
#define AWS_IOT_SHADOW_ENABLE_ASSERTS                                     ( 1 )
#define AWS_IOT_DEFENDER_ENABLE_ASSERTS                                   ( 1 )
#define AWS_IOT_JOBS_ENABLE_ASSERTS                                       ( 1 )
#define AWS_IOT_PROVISIONING_ENABLE_ASSERTS                               ( 1 )

/* Library logging configuration. IOT_LOG_LEVEL_GLOBAL provides a global log
 * level for all libraries; the library-specific settings override the global
 * setting. If both the library-specific and global settings are undefined,
 * no logs will be printed. */
#define IOT_LOG_LEVEL_GLOBAL                                              IOT_LOG_INFO
#define IOT_LOG_LEVEL_DEMO                                                IOT_LOG_INFO
#define IOT_LOG_LEVEL_PLATFORM                                            IOT_LOG_NONE
#define IOT_LOG_LEVEL_NETWORK                                             IOT_LOG_INFO
#define IOT_LOG_LEVEL_TASKPOOL                                            IOT_LOG_NONE
#define IOT_LOG_LEVEL_MQTT                                                IOT_LOG_INFO
#define AWS_IOT_LOG_LEVEL_SHADOW                                          IOT_LOG_INFO
#define AWS_IOT_LOG_LEVEL_DEFENDER                                        IOT_LOG_INFO
#define AWS_IOT_LOG_LEVEL_JOBS                                            IOT_LOG_INFO
#define AWS_IOT_LOG_LEVEL_PROVISIONING                                    IOT_LOG_INFO

/* Default assert and memory allocation functions. */
#include <assert.h>
#include <stdlib.h>

#define Iot_DefaultAssert    assert
#define Iot_DefaultMalloc    malloc
#define Iot_DefaultFree      free

/* The build system will choose the appropriate system types file for the platform
 * layer based on the host operating system. */
#include IOT_SYSTEM_TYPES_FILE

#endif /* ifndef IOT_CONFIG_H_ */
