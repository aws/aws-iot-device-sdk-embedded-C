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

#ifndef _IOT_DEMO_CONFIG_H_
#define _IOT_DEMO_CONFIG_H_

/* Server endpoints used for the demos. May be overridden with command line
 * options. */
#define IOT_DEMO_SECURED_CONNECTION    ( true )
#define IOT_DEMO_SERVER                ""
#define IOT_DEMO_PORT                  ( 443 )

/* Credential paths. May be overridden with command line options. */
#define IOT_DEMO_ROOT_CA               ""
#define IOT_DEMO_CLIENT_CERT           ""
#define IOT_DEMO_PRIVATE_KEY           ""

/* Default Thing Name to use for AWS IoT demos. */
/* #define AWS_IOT_DEMO_THING_NAME                     "" */

/* MQTT demo configuration. */
/* #define IOT_DEMO_MQTT_CLIENT_IDENTIFIER         "" */
#define IOT_DEMO_MQTT_PUBLISH_BURST_COUNT    ( 10 )
#define IOT_DEMO_MQTT_PUBLISH_BURST_SIZE     ( 10 )

/* Enable asserts in linear containers and MQTT. */
#define IOT_CONTAINERS_ENABLE_ASSERTS        ( 1 )
#define IOT_MQTT_ENABLE_ASSERTS              ( 1 )

/* Library logging configuration. */
#define IOT_LOG_LEVEL_DEMO                   IOT_LOG_INFO
#define IOT_LOG_LEVEL_GLOBAL                 IOT_LOG_INFO
#define IOT_LOG_LEVEL_PLATFORM               IOT_LOG_INFO
#define IOT_LOG_LEVEL_NETWORK                IOT_LOG_INFO
#define IOT_LOG_LEVEL_MQTT                   IOT_LOG_INFO
#define AWS_IOT_LOG_LEVEL_SHADOW             IOT_LOG_INFO

/* The build system will choose the appropriate system types file for the platform
 * layer based on the host operating system. */
#include IOT_SYSTEM_TYPES_FILE

#endif /* ifndef _IOT_DEMO_CONFIG_H_ */
