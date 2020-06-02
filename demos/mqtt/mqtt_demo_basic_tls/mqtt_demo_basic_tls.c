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

/*
 * Demo for showing the use of MQTT APIs to establish an MQTT session,
 * subscribe to a topic, publish to a topic, receive incoming publishes,
 * unsubscribe from a topic and disconnect the MQTT session.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS2 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBREC
 * are resend in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBREC is received.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX socket includes. */
#include <netdb.h>
#include <poll.h>
#include <time.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

/* MQTT API header. */
#include "mqtt.h"
#include "mqtt_state.h"

/* Demo Config header. */
#include "demo_config.h"

/**
 * @brief MQTT server host name.
 *
 * This demo uses the Mosquitto test server. This is a public MQTT server; do not
 * publish anything sensitive to this server.
 */
#define BROKER_ENDPOINT            "test.mosquitto.org"

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH     ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief MQTT server port number.
 *
 * In general, port 8883 is for secured MQTT connections.
 */
#define BROKER_PORT                ( 8883 )

/**
 * @brief Path of the file containing the server's root CA certificate.
 *
 * This certificate should be PEM-encoded.
 */
#define SERVER_CERT_PATH           "certificates/mosquitto.org.crt"

/**
 * @brief Length of path to server certificate.
 */
#define SERVER_CERT_PATH_LENGTH    ( ( uint16_t ) ( sizeof( SERVER_CERT_PATH ) - 1 ) )

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define NETWORK_BUFFER_SIZE        ( 1024U )

/* Check that client identifier is defined. */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH            ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS             ( 1000 )

/**
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define MQTT_EXAMPLE_TOPIC                  CLIENT_IDENTIFIER "/example/topic"

/**
 * @brief Length of client MQTT topic.
 */
#define MQTT_EXAMPLE_TOPIC_LENGTH           ( ( uint16_t ) ( sizeof( MQTT_EXAMPLE_TOPIC ) - 1 ) )

/**
 * @brief The MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE                "Hello World!"

/**
 * @brief The MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE_LENGTH         ( ( uint16_t ) ( sizeof( MQTT_EXAMPLE_MESSAGE ) - 1 ) )

/**
 * @brief Maximum number of outgoing publishes maintained in the application
 * until an ack is received from the broker.
 */
#define MAX_OUTGOING_PUBLISHES              ( 5U )

/**
 * @brief Invalid packet identifier for the MQTT packets. Zero is always an
 * invalid packet identifier as per MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_ID_INVALID              ( ( uint16_t ) 0U )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 *
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 500U )

/**
 * @brief Time interval in seconds at which an MQTT PINGREQ need to be sent to
 * broker.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS    ( 60U )

/**
 * @brief Delay between MQTT publishes in seconds.
 */
#define DELAY_BETWEEN_PUBLISHES_SECONDS     ( 1U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 20 )

/*-----------------------------------------------------------*/

/**
 * @brief Structure to keep the MQTT publish packets until an ack is received
 * for QoS2 publishes.
 */
typedef struct PublishPackets
{
    /**
     * @brief MQTT client identifier. Must be unique per client.
     */
    uint16_t packetId;

    /**
     * @brief MQTT client identifier. Must be unique per client.
     */
    MQTTPublishInfo_t pubInfo;
} PublishPackets_t;

/*-----------------------------------------------------------*/

/**
 * @brief globalEntryTime entry time into the application to use as a reference
 * timestamp in #getTimeMs function. #getTimeMs will always return the difference
 * of current time with the globalEntryTime. This will reduce the chances of
 * overflow for 32 bit unsigned integer used for holding the timestamp.
 *
 */
static uint32_t globalEntryTimeMs = 0U;

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted subscribe.
 */
static uint16_t globalSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe response to the transmitted unsubscribe
 * request.
 */
static uint16_t globalUnsubscribePacketIdentifier = 0U;

/**
 * @brief Array to keep the outgoing publish messages.
 * These stored outgoing publish messages are used to keep the messages until
 * a successful ack is received.
 */
static PublishPackets_t outgoingPublishPackets[ MAX_OUTGOING_PUBLISHES ] = { 0 };

/*-----------------------------------------------------------*/

/**
 * @brief Creates a TCP connection to the MQTT broker as specified by
 * BROKER_ENDPOINT and BROKER_PORT defined at the top of this file.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 * @param[out] pTcpSocket Pointer to TCP socket file descriptor.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pTcpSocket );

/**
 * @brief Set up a TLS connection over an existing TCP connection.
 *
 * @param[in] tcpSocket Existing TCP connection.
 * @param[out] pSslContext Pointer to SSL connection context pointer.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int tlsSetup( int tcpSocket,
                     SSL ** pSslContext );

/**
 * @brief The transport send function provided to the MQTT context.
 *
 * @param[in] pSslContext Pointer to SSL context.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToSend Length of data to send.
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportSend( MQTTNetworkContext_t pSslContext,
                              const void * pMessage,
                              size_t bytesToSend );

/**
 * @brief The transport receive function provided to the MQTT context.
 *
 * @param[in] pSslContext Pointer to SSL context.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToRecv Length of data to be received.
 *
 * @return Number of bytes received; negative value on error;
 * 0 for timeout.
 */
static int32_t transportRecv( MQTTNetworkContext_t pSslContext,
                              void * pBuffer,
                              size_t bytesToRecv );

/**
 * @brief The timer query function provided to the MQTT context.
 *
 * This function returns the elapsed time with reference to #globalEntryTimeMs.
 *
 * @return Time in milliseconds.
 */
static uint32_t getTimeMs( void );

/**
 * @brief The function to handle the incoming publishes.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] packetIdentifier Packet identifier of the incoming publish.
 */
static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo,
                                   uint16_t packetIdentifier );

/**
 * @brief The application callback function for getting the incoming publish
 * and incoming acks reported from MQTT library.
 *
 * @param[in] pContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] packetIdentifier Packet identifier of the incoming packet.
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket..
 *
 * @param[in] pContext MQTT context pointer.
 * @param[in] pSslContext SSL context.
 * @param[in] createCleanSession Creates a new MQTT session if true.
 * If false, tries to establish the existing session if there was session
 * already present in broker.
 * @param[out] pSessionPresent Session was already present in the broker or not.
 * Session present response is obtained from the CONNACK from broker.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pContext,
                                 SSL * pSslContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent );

/**
 * @brief Close an MQTT session by sending MQTT DISCONNECT.
 *
 * @param[in] pContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if DISCONNECT was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int disconnectMqttSession( MQTTContext_t * pContext );

/**
 * @brief Sends an MQTT SUBSCRIBE to subscribe to #MQTT_EXAMPLE_TOPIC
 * defined at the top of the file.
 *
 * @param[in] pContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if SUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int subscribeToTopic( MQTTContext_t * pContext );

/**
 * @brief Sends an MQTT UNSUBSCRIBE to unsubscribe from
 * #MQTT_EXAMPLE_TOPIC defined at the top of the file.
 *
 * @param[in] pContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if UNSUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static MQTTStatus_t unsubscribeFromTopic( MQTTContext_t * pContext );

/**
 * @brief Sends an MQTT PUBLISH to #MQTT_EXAMPLE_TOPIC defined at
 * the top of the file.
 *
 * @param[in] pContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if PUBLISH was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int publishToTopic( MQTTContext_t * pContext );

/**
 * @brief Function to get the free index at which an outgoing publish
 * can be stored.
 *
 * @param[out] pIndex The pointer to index at which an outgoing publish message
 * can be stored.
 *
 * @return EXIT_FAILURE if no more publishes can be stored;
 * EXIT_SUCCESS if an index to store the next outgoing publish is obtained.
 */
static int getNextFreeIndexForOutgoingPublishes( uint8_t * pIndex );

/**
 * @brief Function to clean up an outgoing publish at given index from the
 * #outgoingPublishPackets array.
 *
 * @param[in] index The index at which a publish message has to be cleaned up.
 */
static void cleanupOutgoingPublishAt( uint8_t index );

/**
 * @brief Function to clean up all the outgoing publishes maintained in the
 * array.
 */
static void cleanUpOutgoingPublishes();

/**
 * @brief Function to clean up the publish packet with the given packet id.
 *
 * @param[in] packetId Packet identifier of the packet to be cleaned up from
 * the array.
 */
static void cleanupOutgoingPublishesWithPacketID( uint16_t packetId );

/**
 * @brief Function to get the index of packet in the array with
 * the given packet id.
 *
 * @param[in] packetId Packet identifier of the packet get the index for.
 *
 * @return #MAX_OUTGOING_PUBLISHES if no index found; index of the publish
 * packet if a packet is found.
 */
static uint8_t getIndexOfOutgoingPublishWithPacketId( uint16_t packetId );

/**
 * @brief Function to resend the publishes if a session is re-established with
 * the broker. This function handles the resending of the QoS2 publish packets,
 * which are in state #MQTTPubrecPending.
 *
 * @param[in] pContext MQTT context pointer.
 */
static int handlePublishResend( MQTTContext_t * pContext );

/*-----------------------------------------------------------*/

static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pTcpSocket )
{
    int status = EXIT_SUCCESS;
    struct addrinfo hints, * pIndex, * pListHead = NULL;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;
    struct timeval transportTimeout;

    /* Add hints to retrieve only TCP sockets in getaddrinfo. */
    ( void ) memset( &hints, 0x00, sizeof( hints ) );
    /* Address family of either IPv4 or IPv6. */
    hints.ai_family = AF_UNSPEC;
    /* TCP Socket. */
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    /* Perform a DNS lookup on the given host name. */
    status = getaddrinfo( pServer, NULL, &hints, &pListHead );

    if( status != -1 )
    {
        /* Attempt to connect to one of the retrieved DNS records. */
        for( pIndex = pListHead; pIndex != NULL; pIndex = pIndex->ai_next )
        {
            *pTcpSocket = socket( pIndex->ai_family, pIndex->ai_socktype, pIndex->ai_protocol );

            if( *pTcpSocket == -1 )
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

            status = connect( *pTcpSocket, pServerInfo, serverInfoLength );

            if( status == -1 )
            {
                close( *pTcpSocket );
            }
            else
            {
                break;
            }
        }

        if( pIndex == NULL )
        {
            /* Fail if no connection could be established. */
            status = EXIT_FAILURE;
            LogError( ( "Located but could not connect to MQTT broker %.*s.",
                        ( int ) strlen( pServer ),
                        pServer ) );
        }
        else
        {
            status = EXIT_SUCCESS;
            LogInfo( ( "TCP connection established with %.*s.\n\n",
                       ( int ) strlen( pServer ),
                       pServer ) );
        }
    }
    else
    {
        LogError( ( "Could not locate MQTT broker %.*s.",
                    ( int ) strlen( pServer ),
                    pServer ) );
        status = EXIT_FAILURE;
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return status;
}

/*-----------------------------------------------------------*/

static int tlsSetup( int tcpSocket,
                     SSL ** pSslContext )
{
    int status = EXIT_FAILURE, sslStatus = 0;
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    assert( tcpSocket >= 0 );

    /* Setup for creating a TLS client. */
    SSL_CTX * pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        /* OpenSSL does not provide a single function for reading and loading certificates
         * from files into stores, so the file API must be called. */
        pRootCaFile = fopen( SERVER_CERT_PATH, "r" );

        if( pRootCaFile != NULL )
        {
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );
        }
        else
        {
            LogError( ( "Unable to find the certificate file in the path"
                        " provided by SERVER_CERT_PATH(%.*s).",
                        SERVER_CERT_PATH_LENGTH,
                        SERVER_CERT_PATH ) );
        }

        if( pRootCa != NULL )
        {
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslSetup ),
                                             pRootCa );
        }
        else
        {
            LogError( ( "Failed to parse the server certificate from"
                        " file %.*s. Please validate the certificate.",
                        SERVER_CERT_PATH_LENGTH,
                        SERVER_CERT_PATH ) );
        }
    }

    /* Set up the TLS connection. */
    if( sslStatus == 1 )
    {
        /* Create a new SSL context. */
        *pSslContext = SSL_new( pSslSetup );

        if( *pSslContext != NULL )
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( *pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( *pSslContext, tcpSocket );
        }
        else
        {
            LogError( ( "Failed to create a new SSL context." ) );
            sslStatus = 0;
        }

        /* Perform the TLS handshake. */
        if( sslStatus == 1 )
        {
            sslStatus = SSL_connect( *pSslContext );
        }
        else
        {
            LogError( ( "Failed to set the socket fd to SSL context." ) );
        }

        if( sslStatus == 1 )
        {
            if( SSL_get_verify_result( *pSslContext ) != X509_V_OK )
            {
                sslStatus = 0;
            }
        }
        else
        {
            LogError( ( "Failed to perform TLS handshake." ) );
        }

        /* Clean up on error. */
        if( sslStatus == 0 )
        {
            SSL_free( *pSslContext );
            *pSslContext = NULL;
        }
    }
    else
    {
        LogError( ( "Failed to add certificate to store." ) );
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

    /* Log failure or success and update the correct exit status to return. */
    if( sslStatus == 0 )
    {
        LogError( ( "Failed to establish a TLS connection to %.*s.",
                    BROKER_ENDPOINT_LENGTH,
                    BROKER_ENDPOINT ) );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection to %.*s.\n\n",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT ) );
        status = EXIT_SUCCESS;
    }

    return status;
}

/*-----------------------------------------------------------*/

static int32_t transportSend( MQTTNetworkContext_t pSslContext,
                              const void * pMessage,
                              size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLOUT,
        .revents = 0
    };

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pSslContext );

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pSslContext, pMessage, bytesToSend );
    }
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Timed out while polling SSL socket for write buffer availability." ) );
    }
    else
    {
        LogError( ( "Polling of the SSL socket for write buffer availability failed"
                    " with status %d.",
                    pollStatus ) );
        bytesSent = -1;
    }

    return bytesSent;
}

/*-----------------------------------------------------------*/

static int32_t transportRecv( MQTTNetworkContext_t pSslContext,
                              void * pBuffer,
                              size_t bytesToRecv )
{
    int32_t bytesReceived = 0;
    int pollStatus = -1, bytesAvailableToRead = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLIN | POLLPRI,
        .revents = 0
    };

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pSslContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pSslContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );
    }

    /* SSL read of data. */
    if( ( pollStatus > 0 ) || ( bytesAvailableToRead > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pSslContext, pBuffer, bytesToRecv );
    }
    /* Poll timed out. */
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Poll timed out and there is no data to read from the buffer." ) );
    }
    else
    {
        LogError( ( "Poll returned with status = %d.", pollStatus ) );
        bytesReceived = -1;
    }

    return bytesReceived;
}

/*-----------------------------------------------------------*/

static uint32_t getTimeMs( void )
{
    uint32_t timeMs;
    struct timespec timeSpec;

    /* Get the MONOTONIC time. */
    clock_gettime( CLOCK_MONOTONIC, &timeSpec );

    /* Calculate the milliseconds from timespec. */
    timeMs = ( uint32_t ) ( timeSpec.tv_sec * 1000 )
             + ( uint32_t ) ( timeSpec.tv_nsec / ( 1000 * 1000 ) );

    /* Reduce globalEntryTime from obtained time so as to always return the
     * elapsed time in the application. */
    timeMs = ( uint32_t ) ( timeMs - globalEntryTimeMs );

    return timeMs;
}

/*-----------------------------------------------------------*/

static int getNextFreeIndexForOutgoingPublishes( uint8_t * pIndex )
{
    int status = EXIT_FAILURE;

    assert( outgoingPublishPackets != NULL );

    for( *pIndex = 0; *pIndex < MAX_OUTGOING_PUBLISHES; ( *pIndex )++ )
    {
        /* A free index is marked byy invalid packet id.
         * Check if the the index has a free slot. */
        if( outgoingPublishPackets[ *pIndex ].packetId == MQTT_PACKET_ID_INVALID )
        {
            status = EXIT_SUCCESS;
            break;
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishAt( uint8_t index )
{
    assert( outgoingPublishPackets != NULL );
    assert( index < MAX_OUTGOING_PUBLISHES );

    /* Clean up all the entries. */
    if( index < MAX_OUTGOING_PUBLISHES )
    {
        /* Assign the packet ID to zero. */
        outgoingPublishPackets[ index ].packetId = MQTT_PACKET_ID_INVALID;

        /* Clear the publish info. */
        ( void ) memset( &( outgoingPublishPackets[ index ].pubInfo ),
                         0x00,
                         sizeof( outgoingPublishPackets[ index ].pubInfo ) );
    }
}

/*-----------------------------------------------------------*/

static void cleanUpOutgoingPublishes()
{
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );

    /* Clean up all the saved outgoing publishes. */
    for( ; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        cleanupOutgoingPublishAt( index );
    }
}

/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishesWithPacketID( uint16_t packetId )
{
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );

    /* Clean up all the saved outgoing publishes. */
    for( ; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId == packetId )
        {
            cleanupOutgoingPublishAt( index );
            LogInfo( ( "Cleaned up outgoing publish packet with packet id %u.\n\n",
                       packetId ) );
            break;
        }
    }
}

/*-----------------------------------------------------------*/

static uint8_t getIndexOfOutgoingPublishWithPacketId( uint16_t packetId )
{
    uint8_t index = 0U;

    assert( outgoingPublishPackets != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );

    /* Find the index for the given packet id. */
    for( ; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId == packetId )
        {
            break;
        }
    }

    return index;
}

/*-----------------------------------------------------------*/

/**
 * @brief Function to clean up the publish packet with the given packet id.
 *
 * @param[in] packetId Packet identifier of the packet to be cleaned up from
 * the array.
 */
static int handlePublishResend( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;
    MQTTStateCursor_t cursor = 0U;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint8_t index = MAX_OUTGOING_PUBLISHES;

    assert( outgoingPublishPackets != NULL );

    /* Check all the QoS2 publish packets that are still waiting for
     * a PUBREC. This can be identified by querying the state machine
     * for all the outgoing publish packets which are in state
     * #MQTTPubRecPending. */
    do
    {
        /* Find the packet ids which are in #MQTTPubRecPending state.
         * Using the same cursor will help restart the search from the
         * last searched position. */
        packetId = MQTT_StateSelect( pContext, MQTTPubRecPending, &cursor );

        /* Check if a valid packet id is obtained. */
        if( packetId != MQTT_PACKET_ID_INVALID )
        {
            /* Resending the publish after marking publish as duplicate. */
            index = getIndexOfOutgoingPublishWithPacketId( packetId );

            /* Check if a valid index is obtained. */
            if( index < MAX_OUTGOING_PUBLISHES )
            {
                /*Resend the publish after marking it as duplicate. */
                outgoingPublishPackets[ index ].pubInfo.dup = true;

                LogInfo( ( "Sending duplicate PUBLISH with packet id %u.",
                           packetId ) );
                mqttStatus = MQTT_Publish( pContext,
                                           &outgoingPublishPackets[ index ].pubInfo,
                                           packetId );

                if( mqttStatus != MQTTSuccess )
                {
                    LogError( ( "Sending duplicate PUBLISH for packet id %u "
                                " failed with status %u.",
                                packetId,
                                mqttStatus ) );
                    status = EXIT_FAILURE;
                    break;
                }
                else
                {
                    LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.\n\n",
                               packetId ) );
                }
            }
            else
            {
                LogError( ( "Failed to obtain a stored outgoing publish packet for"
                            " packet id %u.",
                            packetId ) );
                status = EXIT_FAILURE;
            }
        }
    } while( packetId != MQTT_PACKET_ID_INVALID );

    return status;
}

/*-----------------------------------------------------------*/

static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo,
                                   uint16_t packetIdentifier )
{
    assert( pPublishInfo != NULL );

    /* Process incoming Publish. */
    LogInfo( ( "Incoming QOS : %d.", pPublishInfo->qos ) );

    /* Verify the received publish is for the we have subscribed to. */
    if( ( pPublishInfo->topicNameLength == MQTT_EXAMPLE_TOPIC_LENGTH ) &&
        ( 0 == strncmp( MQTT_EXAMPLE_TOPIC,
                        pPublishInfo->pTopicName,
                        pPublishInfo->topicNameLength ) ) )
    {
        LogInfo( ( "Incoming Publish Topic Name: %.*s matches subscribed topic.",
                   pPublishInfo->topicNameLength,
                   pPublishInfo->pTopicName ) );
        LogInfo( ( "Incoming Publish message Packet Id is %u.",
                   packetIdentifier ) );
        LogInfo( ( "Incoming Publish Message : %.*s.\n\n",
                   ( int ) pPublishInfo->payloadLength,
                   ( const char * ) pPublishInfo->pPayload ) );
    }
    else
    {
        LogInfo( ( "Incoming Publish Topic Name: %.*s does not match subscribed topic.",
                   pPublishInfo->topicNameLength,
                   pPublishInfo->pTopicName ) );
    }
}

/*-----------------------------------------------------------*/

static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo )
{
    assert( pContext != NULL );
    assert( pPacketInfo != NULL );

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pPublishInfo != NULL );
        /* Handle incoming publish. */
        handleIncomingPublish( pPublishInfo, packetIdentifier );
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_SUBACK:
                LogInfo( ( "Subscribed to the topic %.*s.\n\n",
                           MQTT_EXAMPLE_TOPIC_LENGTH,
                           MQTT_EXAMPLE_TOPIC ) );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( globalSubscribePacketIdentifier == packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Unsubscribed from the topic %.*s.\n\n",
                           MQTT_EXAMPLE_TOPIC_LENGTH,
                           MQTT_EXAMPLE_TOPIC ) );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( globalUnsubscribePacketIdentifier == packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* Nothing to be done from application as library handles
                 * PINGRESP. */
                LogInfo( ( "PIGRESP received.\n\n" ) );
                break;

            case MQTT_PACKET_TYPE_PUBREC:
                LogInfo( ( "PUBREC received for packet id %u.",
                           packetIdentifier ) );
                /* Cleanup publish packet when a PUBREC is received. */
                cleanupOutgoingPublishesWithPacketID( packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_PUBREL:

                /* Nothing to be done from application as library handles
                 * PUBREL. */
                LogInfo( ( "PUBREL received for packet id %u.\n\n",
                           packetIdentifier ) );
                break;

            case MQTT_PACKET_TYPE_PUBCOMP:

                /* Nothing to be done from application as library handles
                 * PUBCOMP. */
                LogInfo( ( "PUBCOMP received for packet id %u.\n\n",
                           packetIdentifier ) );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).",
                            pPacketInfo->type ) );
        }
    }
}

/*-----------------------------------------------------------*/

static int establishMqttSession( MQTTContext_t * pContext,
                                 SSL * pSslContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    assert( pContext != NULL );
    assert( pSslContext != NULL );

    /* The network buffer must remain valid for the lifetime of the MQTT context. */
    static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network. Network context is socket file descriptor.*/
    transport.networkContext = pSslContext;
    transport.send = transportSend;
    transport.recv = transportRecv;

    /* Fill the values for network buffer. */
    networkBuffer.pBuffer = buffer;
    networkBuffer.size = NETWORK_BUFFER_SIZE;

    /* Application callbacks for receiving incoming publishes and incoming acks
     * from MQTT library. */
    callbacks.appCallback = eventCallback;

    /* Application callback for getting the time for MQTT library. This time
     * function will be used to calculate intervals in MQTT library.*/
    callbacks.getTime = getTimeMs;

    /* Initialize MQTT library. */
    mqttStatus = MQTT_Init( pContext, &transport, &callbacks, &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        status = EXIT_FAILURE;
        LogError( ( "MQTT init failed with status %u.", mqttStatus ) );
    }
    else
    {
        /* Establish MQTT session with a CONNECT packet. */

        /* If #createCleanSession is true, start with a clean session
         * i.e. direct the MQTT broker to discard any previous session data.
         * If #createCleanSession is false, directs the broker to attempt to
         * reestablish a session which was already present. */
        connectInfo.cleanSession = createCleanSession;

        /* The client identifier is used to uniquely identify this MQTT client to
         * the MQTT broker. In a production device the identifier can be something
         * unique, such as a device serial number. */
        connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
        connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

        /* The interval at which an MQTT PINGREQ needs to be sent out to broker. */
        connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

        /* Username and password for authentication. Not used in this demo. */
        connectInfo.pUserName = NULL;
        connectInfo.userNameLength = 0U;
        connectInfo.pPassword = NULL;
        connectInfo.passwordLength = 0U;

        /* Send MQTT CONNECT packet to broker. */
        mqttStatus = MQTT_Connect( pContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, pSessionPresent );

        if( mqttStatus != MQTTSuccess )
        {
            status = EXIT_FAILURE;
            LogError( ( "Connection with MQTT broker failed with status %u.", mqttStatus ) );
        }
        else
        {
            LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static int disconnectMqttSession( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;

    assert( pContext != NULL );

    /* Send DISCONNECT. */
    MQTTStatus_t mqttStatus = MQTT_Disconnect( pContext );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Sending MQTT DISCONNECT failed with status=%u.",
                    mqttStatus ) );
        status = EXIT_FAILURE;
    }

    return status;
}

/*-----------------------------------------------------------*/

static int subscribeToTopic( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS2. */
    pSubscriptionList[ 0 ].qos = MQTTQoS2;
    pSubscriptionList[ 0 ].pTopicFilter = MQTT_EXAMPLE_TOPIC;
    pSubscriptionList[ 0 ].topicFilterLength = MQTT_EXAMPLE_TOPIC_LENGTH;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pContext );

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 globalSubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "SUBSCRIBE sent for topic %.*s to broker.\n\n",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t unsubscribeFromTopic( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to and unsubscribes from only one topic
     * and uses QOS0. */
    pSubscriptionList[ 0 ].qos = MQTTQoS2;
    pSubscriptionList[ 0 ].pTopicFilter = MQTT_EXAMPLE_TOPIC;
    pSubscriptionList[ 0 ].topicFilterLength = MQTT_EXAMPLE_TOPIC_LENGTH;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pContext );

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                   globalUnsubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE sent for topic %.*s to broker.\n\n",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static int publishToTopic( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttSuccess;
    uint8_t publishIndex = MAX_OUTGOING_PUBLISHES;

    assert( pContext != NULL );

    /* Get the next free index for the outgoing publish. All QoS2 outgoing
     * publishes are stored until a PUBREC is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBREC. */
    status = getNextFreeIndexForOutgoingPublishes( &publishIndex );

    if( status == EXIT_FAILURE )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message.\n\n" ) );
    }
    else
    {
        /* This example publishes to only one topic and uses QOS2. */
        outgoingPublishPackets[ publishIndex ].pubInfo.qos = MQTTQoS2;
        outgoingPublishPackets[ publishIndex ].pubInfo.pTopicName = MQTT_EXAMPLE_TOPIC;
        outgoingPublishPackets[ publishIndex ].pubInfo.topicNameLength = MQTT_EXAMPLE_TOPIC_LENGTH;
        outgoingPublishPackets[ publishIndex ].pubInfo.pPayload = MQTT_EXAMPLE_MESSAGE;
        outgoingPublishPackets[ publishIndex ].pubInfo.payloadLength = MQTT_EXAMPLE_MESSAGE_LENGTH;

        /* Get a new packet id. */
        outgoingPublishPackets[ publishIndex ].packetId = MQTT_GetPacketId( pContext );

        /* Send PUBLISH packet. */
        mqttSuccess = MQTT_Publish( pContext,
                                    &outgoingPublishPackets[ publishIndex ].pubInfo,
                                    outgoingPublishPackets[ publishIndex ].packetId );

        if( status != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.",
                        mqttSuccess ) );
            cleanupOutgoingPublishAt( publishIndex );
            status = EXIT_FAILURE;
        }
        else
        {
            LogInfo( ( "PUBLISH send for topic %.*s to broker with packet id %u.\n\n",
                       MQTT_EXAMPLE_TOPIC_LENGTH,
                       MQTT_EXAMPLE_TOPIC,
                       outgoingPublishPackets[ publishIndex ].packetId ) );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TLS connection established using openSSL.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS2 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBREC
 * are resend in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBREC is received.
 */
int main( int argc,
          char ** argv )
{
    int status = EXIT_SUCCESS, tcpSocket;
    bool sessionPresent, mqttSessionEstablished = false;
    MQTTContext_t context;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    SSL * pSslContext = NULL;
    uint32_t publishCount = 0;
    const uint32_t maxPublishCount = 5U;

    ( void ) argc;
    ( void ) argv;

    /* Get the entry time to application. */
    globalEntryTimeMs = getTimeMs();

    /* Establish a TCP connection with the MQTT broker. This example connects
     * to the MQTT broker as specified in BROKER_ENDPOINT and BROKER_PORT at
     * the top of this file. */
    LogInfo( ( "Creating a TCP connection to %.*s:%d.",
               BROKER_ENDPOINT_LENGTH,
               BROKER_ENDPOINT,
               BROKER_PORT ) );
    status = connectToServer( BROKER_ENDPOINT, BROKER_PORT, &tcpSocket );

    /* Establish TLS connection on top of TCP connection. */
    if( status == EXIT_SUCCESS )
    {
        LogInfo( ( "Creating a TLS connection on top of the TCP connection." ) );
        status = tlsSetup( tcpSocket, &pSslContext );
    }

    /* Establish MQTT session on top of TCP+TLS connection. */
    if( status == EXIT_SUCCESS )
    {
        /* Sends an MQTT Connect packet over the already connected TCP socket
         * tcpSocket, and waits for connection acknowledgment (CONNACK) packet. */
        LogInfo( ( "Creating an MQTT connection to %.*s.",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT ) );
        status = establishMqttSession( &context, pSslContext, false, &sessionPresent );

        if( status == EXIT_SUCCESS )
        {
            /* Keep a flag for indicating if MQTT session is established. This
             * flag will mark that an MQTT DISCONNECT has to be send at the end
             * of the demo even if there are intermediate failures. */
            mqttSessionEstablished = true;
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Check if session is present and if there are any outgoing publishes
         * that need to resend. This is only valid if the broker is
         * re-establishing a session which was already present. */
        if( sessionPresent == true )
        {
            LogInfo( ( "An MQTT session with broker is re-established. "
                       "Resending unacked publishes." ) );

            /* Handle all the resend of publish messages. */
            status = handlePublishResend( &context );
        }
        else
        {
            LogInfo( ( "A clean MQTT connection is established."
                       " Cleaning up all the stored outgoing publishes.\n\n" ) );

            /* Clean up the outgoing publishes waiting for ack as this new
             * connection doesn't re-establish an existing session. */
            cleanUpOutgoingPublishes();
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in MQTT_EXAMPLE_TOPIC at the top of this file by sending a
         * subscribe packet. This client will then publish to the same topic it
         * subscribed to, so it will expect all the messages it sends to the broker
         * to be sent back to it from the broker. This demo uses QOS0 in Subscribe,
         * therefore, the Publish messages received from the broker will have QOS0. */
        LogInfo( ( "Subscribing to the MQTT topic %.*s.",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
        status = subscribeToTopic( &context );
    }

    if( status == EXIT_SUCCESS )
    {
        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet.  This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( &context, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            status = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Publish messages with QOS0, receive incoming messages and
         * send keep alive messages. */
        for( publishCount = 0; publishCount < maxPublishCount; publishCount++ )
        {
            LogInfo( ( "Sending Publish to the MQTT topic %.*s.",
                       MQTT_EXAMPLE_TOPIC_LENGTH,
                       MQTT_EXAMPLE_TOPIC ) );
            status = publishToTopic( &context );

            /* Calling MQTT_ProcessLoop to process incoming publish echo, since
             * application subscribed to the same topic the broker will send
             * publish message back to the application. This function also
             * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
             * has expired since the last MQTT packet sent and receive
             * ping responses. */
            mqttStatus = MQTT_ProcessLoop( &context, MQTT_PROCESS_LOOP_TIMEOUT_MS );

            if( mqttStatus != MQTTSuccess )
            {
                LogWarn( ( "MQTT_ProcessLoop returned with status = %u.",
                           mqttStatus ) );
            }

            LogInfo( ( "Delay before continuing to next iteration.\n\n" ) );

            /* Leave connection idle for some time. */
            sleep( DELAY_BETWEEN_PUBLISHES_SECONDS );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Unsubscribe from the topic. */
        LogInfo( ( "Unsubscribing from the MQTT topic %.*s.",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
        status = unsubscribeFromTopic( &context );
    }

    if( status == EXIT_SUCCESS )
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &context, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            status = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    /* Send an MQTT Disconnect packet over the already connected TCP socket.
     * There is no corresponding response for the disconnect packet. After sending
     * disconnect, client must close the network connection. */
    if( mqttSessionEstablished == true )
    {
        if( status == EXIT_FAILURE )
        {
            /* Returned status is not used to update the local status as there
             * were failures in demo execution. */
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

    /* Log the success message. */
    if( status == EXIT_SUCCESS )
    {
        LogInfo( ( "Demo completed successfully." ) );
    }

    return status;
}

/*-----------------------------------------------------------*/
