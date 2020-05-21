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
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TCP connection established using POSIX sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
 */

/* Config header is included first. */
#include "config.h"

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <time.h>
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
#define BROKER_ENDPOINT           "test.mosquitto.org"

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH    ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief MQTT server port number.
 *
 * In general, port 1883 is for unsecured MQTT connections.
 */
#define BROKER_PORT               ( 1883 )

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define NETWORK_BUFFER_SIZE       ( 1024U )

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
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 *
 * Please note
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

/* @brief errno to check transport error. */
extern int errno;

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
 * @brief The transport send function provided to the MQTT context.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToSend Length of data to send.
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportSend( MQTTNetworkContext_t tcpSocket,
                              const void * pMessage,
                              size_t bytesToSend );

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
 * @param[in] tcpSocket TCP socket.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pContext,
                                 int tcpSocket );

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
    ( void ) memset( &hints, 0, sizeof( hints ) );
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
            LogErrorWithArgs( "Located but could not connect to MQTT broker %.*s.",
                              strlen( pServer ),
                              pServer );
        }
        else
        {
            status = EXIT_SUCCESS;
            LogInfoWithArgs( "TCP connection established with %.*s.",
                             strlen( pServer ),
                             pServer );
        }
    }
    else
    {
        LogErrorWithArgs( "Could not locate MQTT broker %.*s.",
                          strlen( pServer ),
                          pServer );
        status = EXIT_FAILURE;
    }

    /* Set the socket option for send and receive timeouts. */
    if( status == EXIT_SUCCESS )
    {
        transportTimeout.tv_sec = 0;
        transportTimeout.tv_usec = ( TRANSPORT_SEND_RECV_TIMEOUT_MS * 1000 );

        /* Set the receive timeout. */
        if( setsockopt( *pTcpSocket,
                        SOL_SOCKET,
                        SO_RCVTIMEO,
                        ( char * ) &transportTimeout,
                        sizeof( transportTimeout ) ) < 0 )
        {
            LogError( "Setting socket receive timeout failed." );
            status = EXIT_FAILURE;
        }

        /* Set the send timeout. */
        if( setsockopt( *pTcpSocket,
                        SOL_SOCKET,
                        SO_SNDTIMEO,
                        ( char * ) &transportTimeout,
                        sizeof( transportTimeout ) ) < 0 )
        {
            LogError( "Setting socket send timeout failed." );
            status = EXIT_FAILURE;
        }
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return status;
}

/*-----------------------------------------------------------*/

static int32_t transportSend( MQTTNetworkContext_t tcpSocket,
                              const void * pMessage,
                              size_t bytesToSend )
{
    int32_t bytesSend = 0;

    bytesSend = send( ( int ) tcpSocket, pMessage, bytesToSend, 0 );

    if( bytesSend < 0 )
    {
        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate that send was timed out. */
            bytesSend = 0;
        }
    }

    return bytesSend;
}

/*-----------------------------------------------------------*/

static int32_t transportRecv( MQTTNetworkContext_t tcpSocket,
                              void * pBuffer,
                              size_t bytesToRecv )
{
    int32_t bytesReceived = 0;

    bytesReceived = ( int32_t ) recv( tcpSocket, pBuffer, bytesToRecv, 0 );

    if( bytesReceived == 0 )
    {
        /* Server closed the connection, treat it as an error. */
        bytesReceived = -1;
    }
    else if( bytesReceived < 0 )
    {
        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate nothing to receive */
            bytesReceived = 0;
        }
    }
    else
    {
        /* EMPTY else */
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

static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo,
                                   uint16_t packetIdentifier )
{
    assert( pPublishInfo != NULL );

    /* Process incoming Publish. */
    LogInfoWithArgs( "Incoming QOS : %d.", pPublishInfo->qos );

    /* Verify the received publish is for the we have subscribed to. */
    if( ( pPublishInfo->topicNameLength == MQTT_EXAMPLE_TOPIC_LENGTH ) &&
        ( 0 == strncmp( MQTT_EXAMPLE_TOPIC,
                        pPublishInfo->pTopicName,
                        pPublishInfo->topicNameLength ) ) )
    {
        LogInfoWithArgs( "Incoming Publish Topic Name: %.*s matches subscribed topic.",
                         pPublishInfo->topicNameLength,
                         pPublishInfo->pTopicName );
        LogInfoWithArgs( "Incoming Publish Message : %.*s.",
                         pPublishInfo->payloadLength,
                         pPublishInfo->pPayload );
    }
    else
    {
        LogInfoWithArgs( "Incoming Publish Topic Name: %.*s does not match subscribed topic.",
                         pPublishInfo->topicNameLength,
                         pPublishInfo->pTopicName );
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
                LogInfoWithArgs( "Subscribed to the topic %.*s.",
                                 MQTT_EXAMPLE_TOPIC_LENGTH,
                                 MQTT_EXAMPLE_TOPIC );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( globalSubscribePacketIdentifier == packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfoWithArgs( "Unsubscribed from the topic %.*s.",
                                 MQTT_EXAMPLE_TOPIC_LENGTH,
                                 MQTT_EXAMPLE_TOPIC );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( globalUnsubscribePacketIdentifier == packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                LogInfo( "PIGRESP received." );
                break;

            /* Any other packet type is invalid. */
            default:
                LogErrorWithArgs( "Unknown packet type received:(%02x).",
                                  pPacketInfo->type );
        }
    }
}

/*-----------------------------------------------------------*/

static int establishMqttSession( MQTTContext_t * pContext,
                                 int tcpSocket )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    char sessionPresent;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    assert( pContext != NULL );
    assert( tcpSocket >= 0 );

    /* The network buffer must remain valid for the lifetime of the MQTT context. */
    static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network. Network context is socket file descriptor.*/
    transport.networkContext = ( MQTTNetworkContext_t ) tcpSocket;
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
    MQTT_Init( pContext, &transport, &callbacks, &networkBuffer );

    /* Establish MQTT session with a CONNECT packet. */

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    connectInfo.cleanSession = true;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

    /* The interval at which an MQTT PINGREQ needs to be sent out to broker. */
    connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

    /* Username and password for authentication. Not used in this demo. */
    connectInfo.pUserName = NULL;
    connectInfo.userNameLength = 0;
    connectInfo.pPassword = NULL;
    connectInfo.passwordLength = 0;

    /* Send MQTT CONNECT packet to broker. */
    mqttStatus = MQTT_Connect( pContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, &sessionPresent );

    if( mqttStatus != MQTTSuccess )
    {
        status = EXIT_FAILURE;
        LogErrorWithArgs( "Connection with MQTT broker failed with status %u.", mqttStatus );
    }
    else
    {
        LogInfo( "MQTT connection successfully established with broker." );
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
        LogErrorWithArgs( "Sending MQTT DISCONNECT failed with status=%u.",
                          mqttStatus );
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

    /* This example subscribes to only one topic and uses QOS0. */
    pSubscriptionList[ 0 ].qos = MQTTQoS0;
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
        LogErrorWithArgs( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                          mqttStatus );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfoWithArgs( "SUBSCRIBE sent for topic %.*s to broker.",
                         MQTT_EXAMPLE_TOPIC_LENGTH,
                         MQTT_EXAMPLE_TOPIC );
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
    pSubscriptionList[ 0 ].qos = MQTTQoS0;
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
        LogErrorWithArgs( "Failed to send UNSUBSCRIBE packet to broker with error = %u.",
                          mqttStatus );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfoWithArgs( "UNSUBSCRIBE sent for topic %.*s to broker.",
                         MQTT_EXAMPLE_TOPIC_LENGTH,
                         MQTT_EXAMPLE_TOPIC );
    }

    return status;
}

/*-----------------------------------------------------------*/

static int publishToTopic( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;
    MQTTStatus_t mqttSuccess;
    MQTTPublishInfo_t publishInfo;

    assert( pContext != NULL );

    /* Some fields not used by this demo so start with everything at 0. */
    ( void ) memset( ( void * ) &publishInfo, 0x00, sizeof( publishInfo ) );

    /* This example publishes to only one topic and uses QOS0. */
    publishInfo.qos = MQTTQoS0;
    publishInfo.pTopicName = MQTT_EXAMPLE_TOPIC;
    publishInfo.topicNameLength = MQTT_EXAMPLE_TOPIC_LENGTH;
    publishInfo.pPayload = MQTT_EXAMPLE_MESSAGE;
    publishInfo.payloadLength = MQTT_EXAMPLE_MESSAGE_LENGTH;

    /* Send PUBLISH packet. Packet Id is not used for a QoS0 publish.
     * Hence 0 is passed as packet id. */
    mqttSuccess = MQTT_Publish( pContext,
                                &publishInfo,
                                0U );

    if( status != MQTTSuccess )
    {
        LogErrorWithArgs( "Failed to send PUBLISH packet to broker with error = %u.",
                          mqttSuccess );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfoWithArgs( "PUBLISH send for topic %.*s to broker.",
                         MQTT_EXAMPLE_TOPIC_LENGTH,
                         MQTT_EXAMPLE_TOPIC );
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TCP connection established using POSIX sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
 *
 */
int main( int argc,
          char ** argv )
{
    int status = EXIT_SUCCESS, tcpSocket;
    bool mqttSessionEstablished = false;
    MQTTContext_t context;
    MQTTStatus_t mqttStatus;
    uint32_t publishCount = 0;
    const uint32_t maxPublishCount = 5U;

    ( void ) argc;
    ( void ) argv;

    /* Get the entry time to application. */
    globalEntryTimeMs = getTimeMs();

    /* Establish a TCP connection with the MQTT broker. This example connects
     * to the MQTT broker as specified in BROKER_ENDPOINT and BROKER_PORT at
     * the top of this file. */
    LogInfoWithArgs( "Creating a TCP connection to %.*s:%d.",
                     BROKER_ENDPOINT_LENGTH,
                     BROKER_ENDPOINT,
                     BROKER_PORT );
    status = connectToServer( BROKER_ENDPOINT, BROKER_PORT, &tcpSocket );

    /* Establish MQTT session on top of TCP connection. */
    if( status == EXIT_SUCCESS )
    {
        /* Sends an MQTT Connect packet over the already connected TCP socket
         * tcpSocket, and waits for connection acknowledgment (CONNACK) packet. */
        LogInfoWithArgs( "Creating an MQTT connection to %.*s.",
                         BROKER_ENDPOINT_LENGTH,
                         BROKER_ENDPOINT );
        status = establishMqttSession( &context, tcpSocket );

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
        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in MQTT_EXAMPLE_TOPIC at the top of this file by sending a
         * subscribe packet. This client will then publish to the same topic it
         * subscribed to, so it will expect all the messages it sends to the broker
         * to be sent back to it from the broker. This demo uses QOS0 in Subscribe,
         * therefore, the Publish messages received from the broker will have QOS0. */
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
            LogErrorWithArgs( "MQTT_ProcessLoop returned with status = %u.",
                              mqttStatus );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Publish messages with QOS0, receive incoming messages and
         * send keep alive messages. */
        for( publishCount = 0; publishCount < maxPublishCount; publishCount++ )
        {
            LogInfoWithArgs( "Publish to the MQTT topic %.*s.",
                             MQTT_EXAMPLE_TOPIC_LENGTH,
                             MQTT_EXAMPLE_TOPIC );
            status = publishToTopic( &context );

            /* Calling MQTT_ProcessLoop to process incoming publish echo, since
             * application subscribed to the same topic the broker will send
             * publish message back to the application. This function also
             * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
             * has expired since the last MQTT packet sent and receive
             * ping responses. */
            mqttStatus = MQTT_ProcessLoop( &context, MQTT_PROCESS_LOOP_TIMEOUT_MS );
            LogInfoWithArgs( "MQTT_ProcessLoop returned with status = %u.",
                             mqttStatus );

            /* Leave connection idle for some time. */
            sleep( DELAY_BETWEEN_PUBLISHES_SECONDS );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Unsubscribe from the topic. */
        LogInfoWithArgs( "Unsubscribe from the MQTT topic %.*s.",
                         MQTT_EXAMPLE_TOPIC_LENGTH,
                         MQTT_EXAMPLE_TOPIC );
        status = unsubscribeFromTopic( &context );
    }

    if( status == EXIT_SUCCESS )
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &context, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            status = EXIT_FAILURE;
            LogErrorWithArgs( "MQTT_ProcessLoop returned with status = %u.",
                              mqttStatus );
        }
    }

    /* Send an MQTT Disconnect packet over the already connected TCP socket.
     * There is no corresponding response for the disconnect packet. After sending
     * disconnect, client must close the network connection. */
    if( mqttSessionEstablished == true )
    {
        LogInfoWithArgs( "Disconnecting the MQTT connection with %.*s.",
                         BROKER_ENDPOINT_LENGTH,
                         BROKER_ENDPOINT );

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

    /* Close the network connection.  */
    if( tcpSocket != -1 )
    {
        shutdown( tcpSocket, SHUT_RDWR );
        close( tcpSocket );
    }

    /* Log the success message. */
    if( status == EXIT_SUCCESS )
    {
        LogInfo( "Demo completed successfully." );
    }

    return status;
}

/*-----------------------------------------------------------*/
