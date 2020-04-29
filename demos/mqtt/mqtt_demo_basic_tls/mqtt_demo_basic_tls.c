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

/**
 * @brief MQTT server host name.
 *
 * This demo uses the Mosquitto test server. This is a public MQTT server; do not
 * publish anything sensitive to this server.
 */
#define SERVER    "test.mosquitto.org"

/**
 * @brief MQTT server port number.
 *
 * In general, port 8883 is for secured MQTT connections.
 */
#define PORT      8883

/**
 * @brief Path of the file containing the server's root CA certificate.
 *
 * This certificate should be PEM-encoded.
 */
#define SERVER_CERT    "mosquitto.org.crt"

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define NETWORK_BUFFER_SIZE    ( 1024U )

/**
 * @brief MQTT client identifier.
 *
 * No two clients may use the same client identifier simultaneously.
 */
#define CLIENT_IDENTIFIER           "testclient"

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH    ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/*-----------------------------------------------------------*/

/**
 * @brief Establish a TCP connection to the given server.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 *
 * @return A file descriptor representing the TCP socket; -1 on failure.
 */
static int connectToServer( const char * pServer, uint16_t port )
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
 * @brief Set up a TLS connection over an existing TCP connection.
 *
 * @param[in] tcpSocket Existing TCP connection.
 *
 * @return An SSL connection context; NULL on failure.
 */
static SSL * tlsSetup( int tcpSocket )
{
    int sslStatus = 0;
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;
    SSL * pSslContext = NULL;

    /* Read the server root CA certificate. */
    SSL_CTX * pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        /* OpenSSL does not provide a single function for reading and loading certificates
         * from files into stores, so the file API must be called. */
        pRootCaFile = fopen( SERVER_CERT, "r" );

        if( pRootCaFile != NULL )
        {
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );
        }

        if( pRootCa != NULL )
        {
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslSetup ),
                                               pRootCa );
        }
    }

    /* Set up the TLS connection. */
    if( sslStatus == 1 )
    {
        /* Create a new SSL context. */
        pSslContext = SSL_new( pSslSetup );

        if( pSslContext != NULL )
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( pSslContext, tcpSocket );
        }
        else
        {
            sslStatus = 0;
        }

        /* Perform the TLS handshake. */
        if( sslStatus == 1 )
        {
            sslStatus = SSL_connect( pSslContext );
        }

        if( sslStatus == 1 )
        {
            if( SSL_get_verify_result( pSslContext ) != X509_V_OK )
            {
                sslStatus = 0;
            }
        }

        /* Clean up on error. */
        if( sslStatus == 0 )
        {
            SSL_free( pSslContext );
            pSslContext = NULL;
        }
    }

    if( pRootCaFile != NULL )
    {
        ( void ) fclose( pRootCaFile );
    }

    if( pRootCa != NULL )
    {
        X509_free( pRootCa );
    }

    if( pSslSetup != NULL )
    {
        SSL_CTX_free( pSslSetup );
    }

    return pSslContext;
}

/*-----------------------------------------------------------*/

/**
 * @brief The transport send function provided to the MQTT context.
 *
 * @param[in] pSslContext SSL context.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToSend Length of data to send.
 *
 * @return Number of bytes sent; negative value on error.
 */
static int32_t transportSend( SSL * pSslContext, const void * pMessage, size_t bytesToSend )
{
    return ( int32_t ) SSL_write( pSslContext, pMessage, bytesToSend );
}

/*-----------------------------------------------------------*/

/**
 * @brief The transport receive function provided to the MQTT context.
 *
 * @param[in] pSslContext SSL context.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToSend Size of pBuffer.
 *
 * @return Number of bytes received; negative value on error.
 */
static int32_t transportRecv( SSL * pSslContext, void * pBuffer, size_t bytesToRecv )
{
    return ( int32_t ) SSL_read( pSslContext, pBuffer, bytesToRecv );
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
static void eventCallback( MQTTContext_t * pContext, MQTTPacketInfo_t * pPacketInfo )
{

}

/*-----------------------------------------------------------*/

/**
 * @brief Establish an MQTT session over a TCP+TLS connection by sending MQTT CONNECT.
 *
 * @param[in] pContext MQTT context.
 * @param[in] pSslContext SSL context.
 *
 * @return EXIT_SUCCESS if an MQTT session is established; EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pContext, SSL * pSslContext )
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
    transport.networkContext = pSslContext;
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
int main( int argc, char ** argv )
{
    bool mqttSessionEstablished = false;
    int status;
    MQTTContext_t context;
    SSL * pSslContext = NULL;

    /* Establish TCP+TLS connection and MQTT session. */
    int tcpSocket = connectToServer( SERVER, PORT );

    if( tcpSocket == -1 )
    {
        status = EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        pSslContext = tlsSetup( tcpSocket );

        if( pSslContext == NULL )
        {
            status = EXIT_FAILURE;
        }
    }

    if( status == EXIT_SUCCESS )
    {
        status = establishMqttSession( &context, pSslContext );

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

    /* Close TLS session if established. */
    if( pSslContext != NULL )
    {
        /* SSL shutdown should be called twice: once to send "close notify" and
         * once more to receive the peer's "close notify". */
        if( SSL_shutdown( pSslContext ) == 0 )
        {
            ( void ) SSL_shutdown( pSslContext );
        }

        SSL_free( pSslContext );
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
