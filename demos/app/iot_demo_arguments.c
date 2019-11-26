/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_demo_arguments.c
 * @brief Implements a function for retrieving command line arguments.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <limits.h>

/* Error handling include. */
#include "iot_error.h"

/* Common demo includes. */
#include "iot_demo_arguments.h"
#include "iot_demo_logging.h"

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

    /* Set default identifier if defined. The identifier is used as either the
     * MQTT client identifier or the Thing Name, which identifies this client to
     * the cloud. */
    #ifdef IOT_DEMO_IDENTIFIER
        pArguments->pIdentifier = IOT_DEMO_IDENTIFIER;
    #endif

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

    /* Set default MQTT broker username if defined. */
    #ifdef IOT_DEMO_USER_NAME
        pArguments->pUserName = IOT_DEMO_USER_NAME;
    #endif

    /* Set default MQTT broker password if defined. */
    #ifdef IOT_DEMO_PASSWORD
        pArguments->pPassword = IOT_DEMO_PASSWORD;
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

        /* If the host is connecting to the MQTT broker hosted by AWS IoT Core,
         * there must either be a set of X.509 credentials or a
         * username/password. Therefore, check that here in order to facilitate
         * debugging. For other MQTT brokers, assume that the CLI arguments are
         * as intended.
         */
        if( pArguments->awsIotMqttMode == true )
        {
            if( ( pArguments->pUserName == NULL ) ||
                ( strlen( pArguments->pUserName ) == 0 ) ||
                ( pArguments->pPassword == NULL ) ||
                ( strlen( pArguments->pPassword ) == 0 ) )
            {
                /* Check that a client certificate path was set. */
                if( ( pArguments->pClientCertPath == NULL ) ||
                    ( strlen( pArguments->pClientCertPath ) == 0 ) )
                {
                    IotLogError( "Either username/password or client certificate path must be set. Exiting." );

                    IOT_SET_AND_GOTO_CLEANUP( false );
                }

                /* Check that a client certificate private key was set. */
                if( ( pArguments->pPrivateKeyPath == NULL ) ||
                    ( strlen( pArguments->pPrivateKeyPath ) == 0 ) )
                {
                    IotLogError( "Either username/password or private key path must be set. Exiting." );

                    IOT_SET_AND_GOTO_CLEANUP( false );
                }
            }
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

    /* Check that the length of the encoded username, if any, will be within
     * the specification of the MQTT standard. */
    if( pArguments->pUserName != NULL )
    {
        if( strlen( pArguments->pUserName ) > UINT16_MAX )
        {
            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    }

    /* Check that the length of the encoded username, if any, will be within
     * the specification of the MQTT standard. */
    if( pArguments->pPassword != NULL )
    {
        if( strlen( pArguments->pPassword ) > UINT16_MAX )
        {
            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    }

    /* No cleanup is required for this function. */
    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

bool IotDemo_ParseArguments( int argc,
                             char ** argv,
                             IotDemoArguments_t * pArguments )
{
    int i = 1;
    const char * pOption = NULL;
    unsigned long int port = 0;
    size_t optionLength = 0;

    /* Load the default demo arguments from the demo config header. */
    _setDefaultArguments( pArguments );

    for( i = 1; i < argc; i++ )
    {
        /* Get argument string and length. */
        pOption = argv[ i ];
        optionLength = strlen( pOption );

        /* Valid options have the format "-X", so they must be 2 characters long. */
        if( optionLength != 2 )
        {
            IotLogWarn( "Ignoring invalid option %s.", pOption );

            continue;
        }

        /* The first character of a valid option must be '-'. */
        if( pOption[ 0 ] != '-' )
        {
            IotLogWarn( "Ignoring invalid option %s.", pOption );

            continue;
        }

        switch( pOption[ 1 ] )
        {
            /* Client certificate path. */
            case 'c':
                i++;
                pArguments->pClientCertPath = argv[ i ];
                break;

            /* Server. */
            case 'h':
                i++;
                pArguments->pHostName = argv[ i ];
                break;

            /* Client identifier or Thing Name. */
            case 'i':
                i++;
                pArguments->pIdentifier = argv[ i ];
                break;

            /* Client certificate private key path. */
            case 'k':
                i++;
                pArguments->pPrivateKeyPath = argv[ i ];
                break;

            /* Username for MQTT. */
            case 'm':
                i++;
                pArguments->pUserName = argv[ i ];
                break;

            /* MQTT server is not AWS. */
            case 'n':
                pArguments->awsIotMqttMode = false;
                break;

            /* Server port. */
            case 'p':
                i++;

                /* Convert argument string to unsigned int. */
                port = strtoul( argv[ i ], NULL, 10 );

                /* Check that port is valid. */
                if( ( port == 0 ) || ( port > UINT16_MAX ) )
                {
                    IotLogWarn( "Ignoring invalid port %lu.", port );
                }
                else
                {
                    pArguments->port = ( uint16_t ) port;
                }

                break;

            /* Root CA path. */
            case 'r':
                i++;
                pArguments->pRootCaPath = argv[ i ];
                break;

            /* Secured connection. */
            case 's':
                pArguments->securedConnection = true;
                break;

            /* Unsecured connection. */
            case 'u':
                pArguments->securedConnection = false;
                break;

            /* Password for MQTT. */
            case 'w':
                i++;
                pArguments->pPassword = argv[ i ];
                break;

            default:
                IotLogWarn( "Ignoring unknown option %s.", pOption );
                break;
        }
    }

    return _validateArguments( pArguments );
}

/*-----------------------------------------------------------*/
