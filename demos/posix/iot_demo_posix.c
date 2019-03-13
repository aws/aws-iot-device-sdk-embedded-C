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
 * @file iot_demo_posix.c
 * @brief Generic demo runner for POSIX systems.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <stdbool.h>
#include <stdlib.h>
#include <unistd.h>

/* Common libraries include. */
#include "iot_common.h"

/* Common demo includes. */
#include "iot_demo_arguments.h"
#include "iot_demo_logging.h"

/* POSIX+OpenSSL network include. */
#include "posix/iot_network_openssl.h"

/*-----------------------------------------------------------*/

/* The demo function to run. This links to a different function depending on
 * the demo. */
extern int RunDemo( bool awsIotMqttMode,
                    const char * pIdentifier,
                    void * pNetworkServerInfo,
                    void * pNetworkCredentialInfo,
                    const IotNetworkInterface_t * pNetworkInterface );

/*-----------------------------------------------------------*/

int main( int argc,
          char ** argv )
{
    /* Return value of this function and the exit status of this program. */
    int status = EXIT_SUCCESS;

    /* Status returned from network stack initialization. */
    IotNetworkError_t networkInitStatus = IOT_NETWORK_SUCCESS;

    /* Arguments for this demo. */
    IotDemoArguments_t demoArguments = IOT_DEMO_ARGUMENTS_INITIALIZER;

    /* Network server info and credentials. */
    IotNetworkServerInfoOpenssl_t serverInfo = IOT_NETWORK_SERVER_INFO_OPENSSL_INITIALIZER;
    IotNetworkCredentialsOpenssl_t credentials = AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER,
                                   * pCredentials = NULL;

    /* Set default identifier if defined. The identifier is used as either the
     * MQTT client identifier or the Thing Name, which identifies this client to
     * the cloud. */
    #ifdef IOT_DEMO_IDENTIFIER
        demoArguments.pIdentifier = IOT_DEMO_IDENTIFIER;
    #endif

    /* Parse any command line arguments. */
    if( IotDemo_ParseArguments( argc,
                                argv,
                                &demoArguments ) == true )
    {
        /* Set the members of the server info. */
        serverInfo.pHostName = demoArguments.pHostName;
        serverInfo.port = demoArguments.port;

        /* For a secured connection, set the members of the credentials. */
        if( demoArguments.securedConnection == true )
        {
            /* Set credential paths. */
            credentials.pClientCertPath = demoArguments.pClientCertPath;
            credentials.pPrivateKeyPath = demoArguments.pPrivateKeyPath;
            credentials.pRootCaPath = demoArguments.pRootCaPath;

            /* By default, the credential initializer enables ALPN with AWS IoT,
             * which only works over port 443. Disable ALPN if another port is
             * used. */
            if( demoArguments.port != 443 )
            {
                credentials.pAlpnProtos = NULL;
            }

            /* Set the pointer to the credentials. */
            pCredentials = &credentials;
        }

        /* Initialize the network stack. */
        networkInitStatus = IotNetworkOpenssl_Init();

        if( networkInitStatus == IOT_NETWORK_SUCCESS )
        {
            /* Run the demo. */
            status = RunDemo( demoArguments.awsIotMqttMode,
                              demoArguments.pIdentifier,
                              &serverInfo,
                              pCredentials,
                              IOT_NETWORK_INTERFACE_OPENSSL );

            /* Clean up the network stack. */
            IotNetworkOpenssl_Cleanup();
        }
        else
        {
            /* Network stack failed to initialize. */
            status = EXIT_FAILURE;
        }
    }
    else
    {
        /* Error parsing arguments. */
        status = EXIT_FAILURE;
    }

    /* Log the demo status. */
    if( status == EXIT_SUCCESS )
    {
        IotLogInfo( "Demo completed successfully." );
    }
    else
    {
        IotLogError( "Error occurred while running demo." );
    }

    return status;
}

/*-----------------------------------------------------------*/
