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
 * @file iot_demo.c
 * @brief Generic demo runner.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* Error handling include. */
#include "private/iot_error.h"

/* Common demo includes. */
#include "iot_demo_arguments.h"
#include "iot_demo_logging.h"

/* Choose the appropriate network header, initializers, and initialization
 * function. */
#if IOT_NETWORK_USE_OPENSSL == 1
    /* POSIX+OpenSSL network include. */
    #include "posix/iot_network_openssl.h"

    #define IOT_DEMO_NETWORK_INTERFACE          IOT_NETWORK_INTERFACE_OPENSSL
    #define IOT_DEMO_SERVER_INFO_INITIALIZER    IOT_NETWORK_SERVER_INFO_OPENSSL_INITIALIZER
    #define IOT_DEMO_CREDENTIALS_INITIALIZER    AWS_IOT_NETWORK_CREDENTIALS_OPENSSL_INITIALIZER

    #define IotDemoNetwork_Init                 IotNetworkOpenssl_Init
    #define IotDemoNetwork_Cleanup              IotNetworkOpenssl_Cleanup
#else
    /* mbed TLS network include. */
    #include "iot_network_mbedtls.h"

    #define IOT_DEMO_NETWORK_INTERFACE          IOT_NETWORK_INTERFACE_MBEDTLS
    #define IOT_DEMO_SERVER_INFO_INITIALIZER    IOT_NETWORK_SERVER_INFO_MBEDTLS_INITIALIZER
    #define IOT_DEMO_CREDENTIALS_INITIALIZER    AWS_IOT_NETWORK_CREDENTIALS_MBEDTLS_INITIALIZER

    #define IotDemoNetwork_Init                 IotNetworkMbedtls_Init
    #define IotDemoNetwork_Cleanup              IotNetworkMbedtls_Cleanup
#endif /* if IOT_NETWORK_USE_OPENSSL == 1 */

/* This file calls a generic placeholder demo function. The build system selects
 * the actual demo function to run by defining it. */
#ifndef RunDemo
    #error "Demo function undefined."
#endif

/*-----------------------------------------------------------*/

/* Declaration of generic demo function. */
extern int RunDemo( bool awsIotMqttMode,
                    const char * pIdentifier,
                    void * pNetworkServerInfo,
                    void * pNetworkCredentialInfo,
                    const IotNetworkInterface_t * pNetworkInterface );

/*-----------------------------------------------------------*/

/**
 * @brief Set the default values of an #IotDemoArguments_t based on compile-time
 * defined constants.
 *
 * @param[out] pArguments Default values will be placed here.
 */
static void _setDefaultArguments( IotDemoArguments_t * pArguments )
{
    /* Default to AWS IoT MQTT mode. */
    pArguments->awsIotMqttMode = true;

    /* Set default secured connection status if defined. */
    #ifdef IOT_DEMO_SECURED_CONNECTION
        pArguments->securedConnection = IOT_DEMO_SECURED_CONNECTION;
    #endif

    /* Set default MQTT server if defined. */
    #ifdef IOT_DEMO_SERVER
        pArguments->pHostName = IOT_DEMO_SERVER;
    #endif

    /* Set default MQTT server port if defined. */
    #ifdef IOT_DEMO_PORT
        pArguments->port = IOT_DEMO_PORT;
    #endif

    /* Set default root CA path if defined. */
    #ifdef IOT_DEMO_ROOT_CA
        pArguments->pRootCaPath = IOT_DEMO_ROOT_CA;
    #endif

    /* Set default client certificate path if defined. */
    #ifdef IOT_DEMO_CLIENT_CERT
        pArguments->pClientCertPath = IOT_DEMO_CLIENT_CERT;
    #endif

    /* Set default client certificate private key path if defined. */
    #ifdef IOT_DEMO_PRIVATE_KEY
        pArguments->pPrivateKeyPath = IOT_DEMO_PRIVATE_KEY;
    #endif
}

/*-----------------------------------------------------------*/

/**
 * @brief Validates the members of an #IotDemoArguments_t.
 *
 * @param[in] pArguments The #IotDemoArguments_t to validate.
 *
 * @return `true` if every member of the #IotDemoArguments_t is valid; `false`
 * otherwise.
 */
static bool _validateArguments( const IotDemoArguments_t * pArguments )
{
    /* Declare a status variable for this function. */
    IOT_FUNCTION_ENTRY( bool, true );

    /* Check that a server was set. */
    if( ( pArguments->pHostName == NULL ) ||
        ( strlen( pArguments->pHostName ) == 0 ) )
    {
        IotLogError( "MQTT server not set. Exiting." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Check that a server port was set. */
    if( pArguments->port == 0 )
    {
        IotLogError( "MQTT server port not set. Exiting." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Check credentials for a secured connection. */
    if( pArguments->securedConnection == true )
    {
        /* Check that a root CA path was set. */
        if( ( pArguments->pRootCaPath == NULL ) ||
            ( strlen( pArguments->pRootCaPath ) == 0 ) )
        {
            IotLogError( "Root CA path not set. Exiting." );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }

        /* Check that a client certificate path was set. */
        if( ( pArguments->pClientCertPath == NULL ) ||
            ( strlen( pArguments->pClientCertPath ) == 0 ) )
        {
            IotLogError( "Client certificate path not set. Exiting." );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }

        /* Check that a client certificate private key was set. */
        if( ( pArguments->pPrivateKeyPath == NULL ) ||
            ( strlen( pArguments->pPrivateKeyPath ) == 0 ) )
        {
            IotLogError( "Client certificate private key not set. Exiting." );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    }
    else
    {
        if( pArguments->awsIotMqttMode == true )
        {
            IotLogError( "AWS IoT does not support unsecured connections." );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    }

    /* No cleanup is required for this function. */
    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

int main( int argc,
          char ** argv )
{
    /* Return value of this function and the exit status of this program. */
    IOT_FUNCTION_ENTRY( int, EXIT_SUCCESS );

    /* Status returned from network stack initialization. */
    IotNetworkError_t networkInitStatus = IOT_NETWORK_SUCCESS;

    /* Flags for tracking which cleanup functions must be called. */
    bool sdkInitialized = false, networkInitialized = false;

    /* Arguments for this demo. */
    IotDemoArguments_t demoArguments = IOT_DEMO_ARGUMENTS_INITIALIZER;

    /* Network server info and credentials. */
    IotNetworkServerInfo_t serverInfo = IOT_DEMO_SERVER_INFO_INITIALIZER;
    IotNetworkCredentials_t credentials = IOT_DEMO_CREDENTIALS_INITIALIZER,
                            * pCredentials = NULL;

    /* Set default identifier if defined. The identifier is used as either the
     * MQTT client identifier or the Thing Name, which identifies this client to
     * the cloud. */
    #ifdef IOT_DEMO_IDENTIFIER
        demoArguments.pIdentifier = IOT_DEMO_IDENTIFIER;
    #endif

    /* Load the default demo arguments from the demo config header. */
    _setDefaultArguments( &demoArguments );

    /* Parse any command line arguments. */
    IotDemo_ParseArguments( argc,
                            argv,
                            &demoArguments );

    /* Validate arguments. */
    if( _validateArguments( &demoArguments ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( EXIT_FAILURE );
    }

    /* Set the members of the server info. */
    serverInfo.pHostName = demoArguments.pHostName;
    serverInfo.port = demoArguments.port;

    /* For a secured connection, set the members of the credentials. */
    if( demoArguments.securedConnection == true )
    {
        /* Set credential paths. */
        credentials.pClientCert = demoArguments.pClientCertPath;
        credentials.pPrivateKey = demoArguments.pPrivateKeyPath;
        credentials.pRootCa = demoArguments.pRootCaPath;

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

    /* Call the SDK initialization function. */
    sdkInitialized = IotSdk_Init();

    if( sdkInitialized == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( EXIT_FAILURE );
    }

    /* Initialize the network stack. */
    networkInitStatus = IotDemoNetwork_Init();

    if( networkInitStatus == IOT_NETWORK_SUCCESS )
    {
        networkInitialized = true;
    }
    else
    {
        IOT_SET_AND_GOTO_CLEANUP( EXIT_FAILURE );
    }

    /* Run the demo. */
    status = RunDemo( demoArguments.awsIotMqttMode,
                      demoArguments.pIdentifier,
                      &serverInfo,
                      pCredentials,
                      IOT_DEMO_NETWORK_INTERFACE );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up the network stack if initialized. */
    if( networkInitialized == true )
    {
        IotDemoNetwork_Cleanup();
    }

    /* Clean up the SDK if initialized. */
    if( sdkInitialized == true )
    {
        IotSdk_Cleanup();
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

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/
