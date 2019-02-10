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

/**
 * @file aws_iot_demo_shadow.c
 * @brief Demonstrates usage of the Thing Shadow library.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <stdbool.h>
#include <string.h>

/* Common demo include. */
#include "iot_demo.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* Shadow include. */
#include "aws_iot_shadow.h"

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Including stdio.h also brings in unwanted (and conflicting) symbols on some
 * platforms. Therefore, any functions in stdio.h needed in this file have an
 * extern declaration here. */
extern int snprintf( char *,
                     size_t,
                     const char *,
                     ... );
/** @endcond */

/**
 * @brief The keep-alive interval used for this demo.
 *
 * An MQTT ping request will be sent periodically at this interval.
 */
#define _KEEP_ALIVE_SECONDS    ( 60 )

/**
 * @brief The timeout for Shadow and MQTT operations in this demo.
 */
#define _TIMEOUT_MS            ( 5000 )

/*-----------------------------------------------------------*/

/**
 * @brief The function that runs the Shadow demo.
 *
 * This function is called to run the Shadow demo once a network connection has
 * been established.
 * @param[in] pThingName NULL-terminated Thing Name to use for this demo.
 * @param[in] pMqttConnection Pointer to the MQTT connection to use. This MQTT
 * connection must be initialized to IOT_MQTT_CONNECTION_INITIALIZER.
 * @param[in] pNetworkInterface Pointer to an MQTT network interface to use.
 * All necessary members of the network interface should be set before calling
 * this function.
 *
 * @return 0 if the demo completes successfully; -1 if some part of it fails.
 */
int AwsIotDemo_RunShadowDemo( const char * const pThingName,
                              IotMqttConnection_t * const pMqttConnection,
                              const IotMqttNetIf_t * const pNetworkInterface )
{
    int status = 0;
    IotMqttError_t mqttStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    /* Set the common members of the connection info. */
    connectInfo.awsIotMqttMode = true;
    connectInfo.cleanSession = true;
    connectInfo.keepAliveSeconds = _KEEP_ALIVE_SECONDS;

    /* AWS IoT recommends the use of the Thing Name as the MQTT client ID. */
    connectInfo.pClientIdentifier = pThingName;
    connectInfo.clientIdentifierLength = ( uint16_t ) strlen( pThingName );

    IotLogInfo( "Shadow Thing Name is %.*s (length %hu).",
                connectInfo.clientIdentifierLength,
                connectInfo.pClientIdentifier,
                connectInfo.clientIdentifierLength );

    /* Establish the MQTT connection. */
    mqttStatus = IotMqtt_Connect( pMqttConnection,
                                  pNetworkInterface,
                                  &connectInfo,
                                  _TIMEOUT_MS );

    if( mqttStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "MQTT CONNECT returned error %s.",
                     IotMqtt_strerror( mqttStatus ) );

        status = -1;
    }

    /* Disconnect the MQTT connection if it was established. */
    if( *pMqttConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotMqtt_Disconnect( *pMqttConnection, false );
    }

    return status;
}

/*-----------------------------------------------------------*/
