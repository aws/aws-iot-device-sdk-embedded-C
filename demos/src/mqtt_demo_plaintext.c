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

#include <stdlib.h>

#include <netdb.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

#include "mqtt.h"

#define SERVER    "test.mosquitto.org"
#define PORT      1883

#define NETWORK_BUFFER_SIZE    ( 1024U )

#define CLIENT_IDENTIFIER           "testclient"
#define CLIENT_IDENTIFIER_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

static int connectToServer( const char * pServer, uint16_t port )
{
    int status, tcpSocket = -1;
    struct addrinfo * pListHead = NULL, * pIndex;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;

    status = getaddrinfo( pServer, NULL, NULL, &pListHead );

    if( status != -1 )
    {
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

static int32_t transportSend( int tcpSocket, const void * pMessage, size_t bytesToSend )
{
    return ( int32_t ) send( tcpSocket, pIndex, bytesRemaining, 0 );
}

static int32_t transportRecv( int tcpSocket, void * pBuffer, size_t bytesToRecv )
{
    return ( int32_t ) recv( tcpSocket, pIndex, bytesRemaining, 0 );
}

static void eventCallback( MQTTContext_t * pContext, MQTTPacketInfo_t * pPacketInfo )
{

}

static uint32_t getTime( void )
{
    return 0;
}

static int establishMqttSession( MQTTContext_t * pContext, int tcpSocket )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;

    /* These members are not copied into the context. They must remain in scope
     * for the lifetime of the context. */
    static MQTTTransportInterface_t transport;
    static MQTTFixedBuffer_t networkBuffer;
    static MQTTApplicationCallbacks_t callbacks;
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

    mqttStatus = MQTT_Connect( pContext, &connectInfo, NULL, NULL );

    if( mqttStatus != MQTTSuccess )
    {
        status = EXIT_FAILURE;
    }

    return status;
}

int main( int argc, char ** argv )
{
    int status;
    MQTTContext_t context;
    int tcpSocket = connectToServer( SERVER, PORT );

    if( tcpSocket != -1 )
    {
        status = establishMqttSession( &context, tcpSocket );
    }
    else
    {
        status = EXIT_FAILURE;
    }

    if( tcpSocket != -1 )
    {
        shutdown( tcpSocket, SHUT_RDWR );
        close( tcpSocket );
    }

    return status;
}
