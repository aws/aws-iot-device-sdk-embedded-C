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

/* Common libraries include. */
#include "iot_common.h"

/* Common demo includes. */
#include "iot_demo.h"
#include "iot_demo_posix.h"

/* POSIX+OpenSSL network include. */
#include "posix/iot_network_openssl.h"

/*-----------------------------------------------------------*/

int main( int argc,
          char ** argv )
{
    bool commonInitialized = false, networkConnectionCreated = false;
    int status = 0;
    IotDemoArguments_t demoArguments = IOT_DEMO_ARGUMENTS_INITIALIZER;
    IotNetworkConnectionOpenssl_t networkConnection = IOT_NETWORK_CONNECTION_OPENSSL_INITIALIZER;
    IotNetworkServerInfoOpenssl_t serverInfo = IOT_NETWORK_SERVER_INFO_OPENSSL_INITIALIZER;
    IotNetworkCredentialsOpenssl_t credentials = AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER, * pCredentials = NULL;
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    IotMqttNetworkInfo_t networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

    /* This function parses arguments and establishes the network connection
     * before running the Shadow demo. */

    /* Set the default Thing Name. */
    #ifdef IOT_DEMO_THING_NAME
        demoArguments.pIdentifier = IOT_DEMO_THING_NAME;
    #endif

    /* Parse any command line arguments. */
    if( IotDemo_ParseArguments( argc,
                                argv,
                                &demoArguments ) == false )
    {
        status = -1;
    }

    /* Initialize the network. */
    if( status == 0 )
    {
        if( IotCommon_Init() == false )
        {
            status = -1;
        }
        else
        {
            if( IotNetworkOpenssl_Init() != IOT_NETWORK_SUCCESS )
            {
                IotCommon_Cleanup();
                status = -1;
            }
            else
            {
                commonInitialized = true;
            }
        }
    }

    /* Thing Name must be set for this demo. */
    if( demoArguments.pIdentifier == NULL )
    {
        IotLogError( "Thing Name must be set for Shadow demo." );

        status = -1;
    }

    if( status == 0 )
    {
        /* Set the TLS connection information for secured connections. Thing
         * Shadow is specific to AWS IoT, so it always requires a secured connection. */
        pCredentials = &credentials;

        /* By default AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER enables ALPN. ALPN
         * must be used with port 443; disable ALPN if another port is being used. */
        if( demoArguments.port != 443 )
        {
            credentials.pAlpnProtos = NULL;
        }

        /* Set the paths to the credentials. Lengths of credential paths are
         * ignored by the POSIX platform layer, so they are not set. */
        credentials.pRootCaPath = demoArguments.pRootCaPath;
        credentials.pClientCertPath = demoArguments.pClientCertPath;
        credentials.pPrivateKeyPath = demoArguments.pPrivateKeyPath;

        /* Set server info. */
        serverInfo.pHostName = demoArguments.pHostName;
        serverInfo.port = demoArguments.port;

        /* Establish a TCP connection to the MQTT server. */
        if( IotNetworkOpenssl_Create( &serverInfo,
                                      pCredentials,
                                      &networkConnection ) != IOT_NETWORK_SUCCESS )
        {
            status = -1;
        }
    }

    if( status == 0 )
    {
        /* Set the MQTT receive callback for a network connection. This receive
         * callback processes MQTT data from the network. */
        if( IotNetworkOpenssl_SetReceiveCallback( &networkConnection,
                                                  IotMqtt_ReceiveCallback,
                                                  &mqttConnection ) != IOT_NETWORK_SUCCESS )
        {
            status = -1;
        }
    }

    if( status == 0 )
    {
        /* Set the members of the network interface used by the MQTT connection. */
        networkInfo.createNetworkConnection = false;
        networkInfo.pNetworkConnection = &networkConnection;
        networkInfo.pNetworkInterface = IOT_NETWORK_INTERFACE_OPENSSL;

        /* Initialize the MQTT library and Shadow library. */
        if( IotMqtt_Init() == IOT_MQTT_SUCCESS )
        {
            if( AwsIotShadow_Init( 0 ) == AWS_IOT_SHADOW_SUCCESS )
            {
                /* Run the Shadow demo. */
                status = AwsIotDemo_RunShadowDemo( demoArguments.pIdentifier,
                                                   &mqttConnection,
                                                   &networkInfo );

                /* Clean up the MQTT library and Shadow library. */
                AwsIotShadow_Cleanup();
            }
            else
            {
                status = -1;
            }

            IotMqtt_Cleanup();
        }
        else
        {
            status = -1;
        }
    }

    /* Close and destroy the network connection (if it was established). */
    if( networkConnectionCreated == true )
    {
        /* Note that the MQTT library may have already closed the connection.
         * However, the network close function is safe to call on a closed connection.
         * On the other hand, the destroy connection function must only be called ONCE.
         */
        IotNetworkOpenssl_Close( &networkConnection );
        IotNetworkOpenssl_Destroy( &networkConnection );
    }

    /* Clean up the network. */
    if( commonInitialized == true )
    {
        IotCommon_Cleanup();
        IotNetworkOpenssl_Cleanup();
    }

    /* Log the demo status. */
    if( status == 0 )
    {
        IotLogInfo( "Demo completed successfully." );
    }
    else
    {
        IotLogError( "Error running demo, status %d.", status );
    }

    return status;
}

/*-----------------------------------------------------------*/
