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
 * @file iot_tests_network.c
 * @brief Common network function implementations for the tests.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <stdbool.h>
#include <string.h>

/* MQTT include. */
#include "iot_mqtt.h"

/* Test network header include. */
#include IOT_TEST_NETWORK_HEADER

/*-----------------------------------------------------------*/

/**
 * @brief Network interface setup function for the tests.
 *
 * Creates a global network connection to be used by the tests.
 * @return true if setup succeeded; false otherwise.
 *
 * @see #IotTest_NetworkCleanup
 */
bool IotTest_NetworkSetup( void );

/**
 * @brief Network interface cleanup function for the tests.
 *
 * @see #IotTest_NetworkSetup
 */
void IotTest_NetworkCleanup( void );

/**
 * @brief Network interface connect function for the tests.
 *
 * Creates a new network connection for use with MQTT.
 *
 * @param[out] pNewConnection The handle by which this new connection will be referenced.
 *
 * @return true if a new network connection was successfully created; false otherwise.
 */
bool IotTest_NetworkConnect( IotTestNetworkConnection_t ** pNewConnection );

/**
 * @brief Network interface close connection function for the tests.
 *
 * @param[in] pNetworkConnection The connection to close. Pass NULL to close
 * the global network connection created by #IotTest_NetworkSetup.
 *
 * @return Always returns #IOT_NETWORK_SUCCESS.
 */
IotNetworkError_t IotTest_NetworkClose( void * pNetworkConnection );

/**
 * @brief Network interface cleanup function for the tests.
 *
 * @param[in] pNetworkConnection The connection to destroy.
 */
void IotTest_NetworkDestroy( void * pNetworkConnection );

/*-----------------------------------------------------------*/

/**
 * @brief The network connection shared among the tests.
 */
static IotTestNetworkConnection_t * _pNetworkConnection = NULL;

/**
 * @brief Network interface to use in the tests.
 */
static const IotNetworkInterface_t * const _pNetworkInterface = IOT_TEST_NETWORK_INTERFACE;

/**
 * @brief The MQTT network interface shared among the tests.
 */
IotMqttNetworkInfo_t _IotTestNetworkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief The MQTT connection shared among the tests.
 */
IotMqttConnection_t _IotTestMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/*-----------------------------------------------------------*/

bool IotTest_NetworkSetup( void )
{
    /* Initialize the network library. */
    if( IotTestNetwork_Init() != IOT_NETWORK_SUCCESS )
    {
        return false;
    }

    if( IotTest_NetworkConnect( &_pNetworkConnection ) == false )
    {
        IotTestNetwork_Cleanup();

        return false;
    }

    /* Set the members of the network info. */
    _IotTestNetworkInfo.createNetworkConnection = false;
    _IotTestNetworkInfo.pNetworkConnection = _pNetworkConnection;
    _IotTestNetworkInfo.pNetworkInterface = _pNetworkInterface;

    return true;
}

/*-----------------------------------------------------------*/

void IotTest_NetworkCleanup( void )
{
    /* Close the TCP connection to the server. */
    if( _pNetworkConnection != NULL )
    {
        IotTest_NetworkClose( NULL );
        IotTest_NetworkDestroy( _pNetworkConnection );
        _pNetworkConnection = NULL;
    }

    /* Clean up the network library. */
    IotTestNetwork_Cleanup();

    /* Clear the network interface. */
    ( void ) memset( &_IotTestNetworkInfo, 0x00, sizeof( IotMqttNetworkInfo_t ) );
}

/*-----------------------------------------------------------*/

bool IotTest_NetworkConnect( IotTestNetworkConnection_t ** pNewConnection )
{
    IotTestNetworkServerInfo_t serverInfo = IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER;
    IotTestNetworkCredentials_t * pCredentials = NULL;

    /* Set up TLS if the endpoint is secured. These tests should always use ALPN. */
    #if IOT_TEST_SECURED_CONNECTION == 1
        IotTestNetworkCredentials_t credentials = IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER;
        pCredentials = &credentials;
    #endif

    /* Open a connection to the test server. */
    if( _pNetworkInterface->create( &serverInfo,
                                    pCredentials,
                                    pNewConnection ) != IOT_NETWORK_SUCCESS )
    {
        return false;
    }

    return true;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotTest_NetworkClose( void * pNetworkConnection )
{
    /* Close the provided network handle; if that is NULL, close the
     * global network handle. */
    if( ( pNetworkConnection != NULL ) &&
        ( pNetworkConnection != _pNetworkConnection ) )
    {
        _pNetworkInterface->close( pNetworkConnection );
    }
    else if( _pNetworkConnection != NULL )
    {
        _pNetworkInterface->close( _pNetworkConnection );
    }

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

void IotTest_NetworkDestroy( void * pNetworkConnection )
{
    if( ( pNetworkConnection != NULL ) &&
        ( pNetworkConnection != _pNetworkConnection ) )
    {
        /* Wrap the network interface's destroy function. */
        _pNetworkInterface->destroy( pNetworkConnection );
    }
    else
    {
        if( _pNetworkConnection != NULL )
        {
            _pNetworkInterface->destroy( _pNetworkConnection );
            _pNetworkConnection = NULL;
        }
    }
}

/*-----------------------------------------------------------*/
