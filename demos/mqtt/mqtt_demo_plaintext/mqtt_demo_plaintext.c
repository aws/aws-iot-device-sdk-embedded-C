/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Standard includes. */
#include <stdlib.h>

/* POSIX socket includes. */
#include <netdb.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

/* MQTT API header. */
#include "mqtt.h"

/* Demo Config header. */
#include "demo_config.h"

/**
 * @brief MQTT server host name.
 *
 * This demo uses the Mosquitto test server. This is a public MQTT server; do not
 * publish anything sensitive to this server.
 */
#define SERVER                 "test.mosquitto.org"

/**
 * @brief MQTT server port number.
 *
 * In general, port 1883 is for unsecured MQTT connections.
 */
#define PORT                   1883

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define NETWORK_BUFFER_SIZE    ( 1024U )

/* Check that client identifier is defined. */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS     ( 1000 )

/*-----------------------------------------------------------*/

/**
 * @brief Establish a TCP connection to the given server.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 *
 * @return A file descriptor representing the TCP socket; -1 on failure.
 */
static int connectToServer( const char * pServer,
                            uint16_t port )
{
    int status, tcpSocket = -1;
    struct addrinfo * pListHead = NULL, * pIndex;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;

    /* Perform a DNS lookup on the given host name. */
    status = getaddrinfo( pServer, NULL, NULL, &pListHead );

    if( status != -1 )
    {
        /* Attempt to connect to one of the retrieved DNS records. */
        for( pIndex = pListHead; pIndex != NULL; pIndex = pIndex->ai_next )
        {
            tcpSocket = socket( pIndex->ai_family, pIndex->ai_socktype, pIndex->ai_protocol );

            if( tcpSocket == -1 )
            {
                continue;
            }

            pServerInfo = pIndex->ai_addr;

            if( pServerInfo->sa_family == AF_INET )
            {
                /* IPv4 */
                ( ( struct sockaddr_in * ) pServerInfo )->sin_port = netPort;
                serverInfoLength = sizeof( struct sockaddr_in );
            }
            else
            {
                /* IPv6 */
                ( ( struct sockaddr_in6 * ) pServerInfo )->sin6_port = netPort;
                serverInfoLength = sizeof( struct sockaddr_in6 );
            }

            status = connect( tcpSocket, pServerInfo, serverInfoLength );

            if( status == -1 )
            {
                close( tcpSocket );
            }
            else
            {
                break;
            }
        }

        if( pIndex == NULL )
        {
            /* Fail if no connection could be established. */
            status = -1;
        }
        else
        {
            status = tcpSocket;
        }
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief The transport send function provided to the MQTT context.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToSend Length of data to send.
 *
 * @return Number of bytes sent; negative value on error.
 */
static int32_t transportSend( MQTTNetworkContext_t tcpSocket,
                              const void * pMessage,
                              size_t bytesToSend )
{
    return ( int32_t ) send( tcpSocket, pMessage, bytesToSend, 0 );
}

/*-----------------------------------------------------------*/

/**
 * @brief The transport receive function provided to the MQTT context.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToSend Size of pBuffer.
 *
 * @return Number of bytes received; negative value on error.
 */
static int32_t transportRecv( MQTTNetworkContext_t tcpSocket,
                              void * pBuffer,
                              size_t bytesToRecv )
{
    return ( int32_t ) recv( tcpSocket, pBuffer, bytesToRecv, 0 );
}

/*-----------------------------------------------------------*/

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * Currently not implemented.
 */
static uint32_t getTime( void )
{
    return 0;
}

/*-----------------------------------------------------------*/

/**
 * @brief MQTT event callback.
 *
 * Currently not implemented.
 */
static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Establish an MQTT session over a TCP connection by sending MQTT CONNECT.
 *
 * @param[in] pContext MQTT context.
 * @param[in] tcpSocket TCP socket.
 *
 * @return EXIT_SUCCESS if an MQTT session is established; EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pContext,
                                 int tcpSocket )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    /* The network buffer must remain valid for the lifetime of the MQTT context. */
    static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

    /* Initialize MQTT context. */
    transport.networkContext = tcpSocket;
    transport.send = transportSend;
    transport.recv = transportRecv;

    networkBuffer.pBuffer = buffer;
    networkBuffer.size = NETWORK_BUFFER_SIZE;

    callbacks.appCallback = eventCallback;
    callbacks.getTime = getTime;

    MQTT_Init( pContext, &transport, &callbacks, &networkBuffer );

    /* Establish MQTT session with a CONNECT packet. */
    connectInfo.cleanSession = true;
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;
    connectInfo.keepAliveSeconds = 0;
    connectInfo.pUserName = NULL;
    connectInfo.userNameLength = 0;
    connectInfo.pPassword = NULL;
    connectInfo.passwordLength = 0;

    mqttStatus = MQTT_Connect( pContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, NULL );

    if( mqttStatus != MQTTSuccess )
    {
        status = EXIT_FAILURE;
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Close an MQTT session by sending MQTT DISCONNECT.
 *
 * @param[in] pContext MQTT context.
 *
 * @return EXIT_SUCCESS if DISCONNECT was successfully sent; EXIT_FAILURE otherwise.
 */
static int disconnectMqttSession( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;

    MQTTStatus_t mqttStatus = MQTT_Disconnect( pContext );

    if( mqttStatus != MQTTSuccess )
    {
        status = EXIT_FAILURE;
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 */
int main( int argc,
          char ** argv )
{
    bool mqttSessionEstablished = false;
    int status = EXIT_SUCCESS;
    MQTTContext_t context;

    /* Establish TCP connection. */
    int tcpSocket = connectToServer( SERVER, PORT );

    if( tcpSocket == -1 )
    {
        status = EXIT_FAILURE;
    }

    /* Establish MQTT session on top of TCP connection. */
    if( status = EXIT_SUCCESS )
    {
        status = establishMqttSession( &context, tcpSocket );

        if( status == EXIT_SUCCESS )
        {
            mqttSessionEstablished = true;
        }
    }

    /* Disconnect MQTT session if established. */
    if( mqttSessionEstablished == true )
    {
        if( status == EXIT_FAILURE )
        {
            ( void ) disconnectMqttSession( &context );
        }
        else
        {
            status = disconnectMqttSession( &context );
        }
    }

    /* Close TCP connection if established. */
    if( tcpSocket != -1 )
    {
        shutdown( tcpSocket, SHUT_RDWR );
        close( tcpSocket );
    }

    return status;
}

/*-----------------------------------------------------------*/
