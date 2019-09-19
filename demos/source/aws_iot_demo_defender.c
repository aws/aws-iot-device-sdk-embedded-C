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

/* Demo configuration includes. */
#include "iot_config.h"

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Demo logging include. */
#include "iot_demo_logging.h"

/* Platform includes for demo. */
#include "platform/iot_clock.h"
#include "platform/iot_network.h"

/* Defender includes. */
#include "aws_iot_defender.h"

/* Includes for initialization. */
#include "iot_mqtt.h"
#include "iot_network_metrics.h"

/**
 * @brief Runs the defender demo.
 *
 * @return AWS_IOT_DEFENDER_SUCCESS on success, otherwise an error code indicating
 *         the cause of error.
 */
static AwsIotDefenderError_t _defenderDemo( const char * pIdentifier,
                                            void * pNetworkServerInfo,
                                            void * pNetworkCredentialInfo,
                                            const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Starts the defender agent.
 *
 * @return AWS_IOT_DEFENDER_SUCCESS on success, otherwise an error code indicating
 *         the cause of error.
 */
static AwsIotDefenderError_t _startDefender( const char * pIdentifier,
                                             void * pNetworkServerInfo,
                                             void * pNetworkCredentialInfo,
                                             const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Callback used to get notification of defender's events.
 */
static void _defenderCallback( void * param1,
                               AwsIotDefenderCallbackInfo_t * const pCallbackInfo );

/*-----------------------------------------------------------*/

int RunDefenderDemo( bool awsIotMqttMode,
                     const char * pIdentifier,
                     void * pNetworkServerInfo,
                     void * pNetworkCredentialInfo,
                     const IotNetworkInterface_t * pNetworkInterface )
{
    int status = EXIT_FAILURE;
    bool initStatus = false;
    IotMqttError_t mqttInitStatus;
    AwsIotDefenderError_t defenderResult;

    /* Unused parameters. */
    ( void ) awsIotMqttMode;

    /* Check parameter(s). */
    if( ( pIdentifier == NULL ) || ( pIdentifier[ 0 ] == '\0' ) )
    {
        IotLogError( "Empty Identifier Use." );
        goto end;
    }

    /* Initialize the MQTT library. */
    mqttInitStatus = IotMqtt_Init();

    if( mqttInitStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "MQTT Initialization Failed." );
        goto end;
    }

    /* Initialize Metrics. */
    initStatus = IotMetrics_Init();

    if( !initStatus )
    {
        IotLogError( "IOT Metrics Initialization Failed." );
        goto mqttCleanup;
    }

    /* Run the demo. */
    defenderResult = _defenderDemo( pIdentifier, pNetworkServerInfo, pNetworkCredentialInfo, pNetworkInterface );

    if( defenderResult == AWS_IOT_DEFENDER_SUCCESS )
    {
        status = EXIT_SUCCESS;
    }

    /* Cleanup. */
    IotMetrics_Cleanup();
mqttCleanup:
    IotMqtt_Cleanup();
end:
    return status;
}

/*-----------------------------------------------------------*/

void _defenderCallback( void * param1,
                        AwsIotDefenderCallbackInfo_t * const pCallbackInfo )
{
    ( void ) param1;

    IotLogInfo( "User's callback is invoked on event %d.", pCallbackInfo->eventType );

    /* Print out the sent metrics report if there is. */
    if( pCallbackInfo->pMetricsReport != NULL )
    {
        IotLogInfo( "Published metrics report." );
    }
    else
    {
        IotLogError( "No metrics report was generated." );
    }

    if( pCallbackInfo->pPayload != NULL )
    {
        IotLogInfo( "Received MQTT message." );
    }
    else
    {
        IotLogError( "No message has been returned from subscribed topic." );
    }
}

/*-----------------------------------------------------------*/

static AwsIotDefenderError_t _defenderDemo( const char * pIdentifier,
                                            void * pNetworkServerInfo,
                                            void * pNetworkCredentialInfo,
                                            const IotNetworkInterface_t * pNetworkInterface )
{
    AwsIotDefenderError_t defenderResult;

    IotLogInfo( "----Device Defender Demo Start----" );

    /* Specify all metrics in "tcp connections" group */
    defenderResult =
        AwsIotDefender_SetMetrics( AWS_IOT_DEFENDER_METRICS_TCP_CONNECTIONS, AWS_IOT_DEFENDER_METRICS_ALL );

    if( defenderResult == AWS_IOT_DEFENDER_SUCCESS )
    {
        /* Set metrics report period to 5 minutes(300 seconds) */
        defenderResult = AwsIotDefender_SetPeriod( 300 );
    }

    if( defenderResult == AWS_IOT_DEFENDER_SUCCESS )
    {
        /* Start the defender agent. */
        defenderResult = _startDefender( pIdentifier, pNetworkServerInfo, pNetworkCredentialInfo, pNetworkInterface );

        if( defenderResult == AWS_IOT_DEFENDER_SUCCESS )
        {
            /* Let it run for 3 seconds */
            IotClock_SleepMs( 3000 );

            /* Stop the defender agent. */
            AwsIotDefender_Stop();
        }
    }

    IotLogInfo( "----Device Defender Demo End. Status: %d----.", defenderResult );

    return defenderResult;
}

/*-----------------------------------------------------------*/

static AwsIotDefenderError_t _startDefender( const char * pIdentifier,
                                             void * pNetworkServerInfo,
                                             void * pNetworkCredentialInfo,
                                             const IotNetworkInterface_t * pNetworkInterface )
{
    const AwsIotDefenderCallback_t callback = { .function = _defenderCallback, .param1 = NULL };
    AwsIotDefenderError_t defenderResult;

    AwsIotDefenderStartInfo_t startInfo = AWS_IOT_DEFENDER_START_INFO_INITIALIZER;

    /* Set network information. */
    startInfo.mqttNetworkInfo = ( IotMqttNetworkInfo_t ) IOT_MQTT_NETWORK_INFO_INITIALIZER;
    startInfo.mqttNetworkInfo.createNetworkConnection = true;
    startInfo.mqttNetworkInfo.u.setup.pNetworkServerInfo = pNetworkServerInfo;
    startInfo.mqttNetworkInfo.u.setup.pNetworkCredentialInfo = pNetworkCredentialInfo;

    /* Set network interface. */
    startInfo.mqttNetworkInfo.pNetworkInterface = pNetworkInterface;

    /* Set MQTT connection information. */
    startInfo.mqttConnectionInfo = ( IotMqttConnectInfo_t ) IOT_MQTT_CONNECT_INFO_INITIALIZER;
    startInfo.mqttConnectionInfo.pClientIdentifier = pIdentifier;
    startInfo.mqttConnectionInfo.clientIdentifierLength = ( uint16_t ) strlen( pIdentifier );

    /* Set Defender callback. */
    startInfo.callback = callback;

    /* Invoke defender start API. */
    defenderResult = AwsIotDefender_Start( &startInfo );

    return defenderResult;
}

/*-----------------------------------------------------------*/
