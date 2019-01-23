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
 * @file aws_iot_demo_shadow_posix.c
 * @brief Runs the Thing Shadow demo on POSIX systems.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <stdbool.h>
#include <stdlib.h>
#include <unistd.h>

/* Shadow include. */
#include "aws_iot_shadow.h"

/* Common demo includes. */
#include "aws_iot_demo.h"
#include "aws_iot_demo_posix.h"

/* Platform layer include. */
#include "platform/aws_iot_network.h"

/*-----------------------------------------------------------*/

int main( int argc,
          char ** argv )
{
    int status = 0;
    AwsIotDemoArguments_t demoArguments = AWS_IOT_DEMO_ARGUMENTS_INITIALIZER;
    AwsIotNetworkConnection_t networkConnection = AWS_IOT_NETWORK_CONNECTION_INITIALIZER;
    AwsIotNetworkTlsInfo_t tlsInfo = AWS_IOT_NETWORK_TLS_INFO_INITIALIZER, * pTlsInfo = NULL;
    AwsIotMqttConnection_t mqttConnection = AWS_IOT_MQTT_CONNECTION_INITIALIZER;
    AwsIotMqttNetIf_t networkInterface = AWS_IOT_MQTT_NETIF_INITIALIZER;

    /* This function parses arguments and establishes the network connection
     * before running the Shadow demo. */

    /* Set the default Thing Name. */
    #ifdef AWS_IOT_DEMO_THING_NAME
        demoArguments.pIdentifier = AWS_IOT_DEMO_THING_NAME;
    #endif

    /* Parse any command line arguments. */
    if( AwsIotDemo_ParseArguments( argc,
                                   argv,
                                   &demoArguments ) == false )
    {
        status = -1;
    }

    /* Initialize the network. */
    if( ( status == 0 ) &&
        ( AwsIotNetwork_Init() != AWS_IOT_NETWORK_SUCCESS ) )
    {
        status = -1;
    }

    /* Thing Name must be set for this demo. */
    if( demoArguments.pIdentifier == NULL )
    {
        AwsIotLogError( "Thing Name must be set for Shadow demo." );

        status = -1;
    }

    if( status == 0 )
    {
        /* Set the TLS connection information for secured connections. Thing
         * Shadow is specific to AWS IoT, so it always requires a secured connection. */
        pTlsInfo = &tlsInfo;

        /* By default AWS_IOT_NETWORK_TLS_INFO_INITIALIZER enables ALPN. ALPN
         * must be used with port 443; disable ALPN if another port is being used. */
        if( demoArguments.port != 443 )
        {
            tlsInfo.pAlpnProtos = NULL;
        }

        /* Set the paths to the credentials. Lengths of credential paths are
         * ignored by the POSIX platform layer, so they are not set. */
        tlsInfo.pRootCa = demoArguments.pRootCaPath;
        tlsInfo.pClientCert = demoArguments.pClientCertPath;
        tlsInfo.pPrivateKey = demoArguments.pPrivateKeyPath;

        /* Establish a TCP connection to the MQTT server. */
        if( AwsIotNetwork_CreateConnection( &networkConnection,
                                            demoArguments.pHostName,
                                            demoArguments.port,
                                            pTlsInfo ) != AWS_IOT_NETWORK_SUCCESS )
        {
            status = -1;
        }
    }

    if( status == 0 )
    {
        /* Set the MQTT receive callback for a network connection. This receive
         * callback processes MQTT data from the network. */
        if( AwsIotNetwork_SetMqttReceiveCallback( networkConnection,
                                                  &mqttConnection,
                                                  AwsIotMqtt_ReceiveCallback ) != AWS_IOT_NETWORK_SUCCESS )
        {
            status = -1;
        }
    }

    if( status == 0 )
    {
        /* Set the members of the network interface used by the MQTT connection. */
        networkInterface.pDisconnectContext = ( void * ) networkConnection;
        networkInterface.pSendContext = ( void * ) networkConnection;
        networkInterface.disconnect = AwsIotNetwork_CloseConnection;
        networkInterface.send = AwsIotNetwork_Send;

        /* Initialize the MQTT library and Shadow library. */
        if( ( AwsIotMqtt_Init() == AWS_IOT_MQTT_SUCCESS ) &&
            ( AwsIotShadow_Init( 0 ) == AWS_IOT_SHADOW_SUCCESS ) )
        {
            /* Run the Shadow demo. */
            status = AwsIotDemo_RunShadowDemo( demoArguments.pIdentifier,
                                               &mqttConnection,
                                               &networkInterface );

            /* Clean up the MQTT library and Shadow library. */
            AwsIotShadow_Cleanup();
            AwsIotMqtt_Cleanup();
        }
        else
        {
            status = -1;
        }
    }

    /* Close and destroy the network connection (if it was established). */
    if( networkConnection != AWS_IOT_NETWORK_CONNECTION_INITIALIZER )
    {
        /* Note that the MQTT library may have called AwsIotNetwork_CloseConnection.
         * However, AwsIotNetwork_CloseConnection is safe to call on a closed connection.
         * On the other hand, AwsIotNetwork_DestroyConnection must only be called ONCE.
         */
        AwsIotNetwork_CloseConnection( networkConnection );
        AwsIotNetwork_DestroyConnection( networkConnection );
    }

    /* Clean up the network. */
    AwsIotNetwork_Cleanup();

    /* Log the demo status. */
    if( status == 0 )
    {
        AwsIotLogInfo( "Demo completed successfully." );
    }
    else
    {
        AwsIotLogError( "Error running demo, status %d.", status );
    }

    return status;
}

/*-----------------------------------------------------------*/
