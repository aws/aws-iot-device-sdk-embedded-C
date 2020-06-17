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
 * Demo for showing use of the MQTT light weight serializer / deserializer
 * API to build simple MQTT client.
 * The Light weight serializer API lets user to serialize and
 * deserialize MQTT messages into a user provided buffer.
 * This API allows use of a statically allocated buffer.
 *
 * The example shown below uses this API to create MQTT messages and
 * send them over the connection established using POSIX sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages.
 *
 */

/* Include demo_config.h first for logging and other configuration */
#include "demo_config.h"

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* POSIX socket includes. */
#include <netdb.h>
#include <unistd.h>
#include <assert.h>
#include <errno.h>
#include <time.h>

#include <sys/socket.h>
#include <sys/types.h>

/* MQTT LightWeight API header. */
#include "mqtt_lightweight.h"

/**
 * @brief MQTT server host name.
 *
 * This demo uses the Mosquitto test server. This is a public MQTT server; do not
 * publish anything sensitive to this server.
 */
#define MQTT_BROKER_ENDPOINT    "test.mosquitto.org"

/**
 * @brief MQTT server port number.
 *
 * In general, port 1883 is for unsecured MQTT connections.
 */
#define MQTT_BROKER_PORT        1883

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#define NETWORK_BUFFER_SIZE     ( 1024U )

/* Check that client identifier is defined. */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define MQTT_EXAMPLE_TOPIC                   CLIENT_IDENTIFIER "/example/topic"

/**
 * @brief Dimensions a file scope buffer currently used to send and receive MQTT data
 * from a socket.
 */
#define SHARED_BUFFER_SIZE                   500U

/**
 * @brief The MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE                 "Hello Light Weight MQTT World!"

/**
 * @brief Keep alive period in seconds for MQTT connection.
 */
#define MQTT_KEEP_ALIVE_PERIOD_SECONDS       5U

/**
 * @brief Socket layer transportTimeout in milliseconds.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS       200U

/**
 * @brief Number of time network receive will be attempted
 * if it fails due to transportTimeout.
 */
#define MQTT_MAX_RECV_ATTEMPTS               10U

/**
 * @brief Delay between two demo iterations.
 */
#define MQTT_DEMO_ITERATION_DELAY_SECONDS    5U

/*-----------------------------------------------------------*/

/**
 * @brief Establish a TCP connection to the given server.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 * @param[out] pSocket pointer to the socket descriptor if connect
 * is successful, this call will return the socket descriptor.
 *
 * @return EXIT_SUCCESS or EXIT_FAILURE.
 */
static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pSocket );

/**
 * @brief Establish an MQTT session over a TCP connection by sending MQTT CONNECT.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serialzing CONNECT packet and deserializing CONN-ACK.
 *
 * @return EXIT_SUCCESS if an MQTT session is established; EXIT_FAILURE otherwise.
 */
static int createMQTTConnectionWithBroker( int tcpSocket,
                                           MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Subscribes to the topic as specified in MQTT_EXAMPLE_TOPIC at the top of
 * this file.
 *
 * @param[in] tcpSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serialzing SUBSCRIBE packet.
 *
 */
static void mqttSubscribeToTopic( int tcpSocket,
                                  MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief  Publishes a message MQTT_EXAMPLE_MESSAGE on MQTT_EXAMPLE_TOPIC topic.
 *
 * @param[in] tcpSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serialzing PUBLISH packet.
 *
 */
static void mqttPublishToTopic( int tcpSocket,
                                MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Unsubscribes from the previously subscribed topic as specified
 * in MQTT_EXAMPLE_TOPIC.
 *
 * @param[in] tcpSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serialzing UNSUBSCRIBE packet.
 *
 */
static void mqttUnsubscribeFromTopic( int tcpSocket,
                                      MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Disconnect From the MQTT broker.
 *
 * @param[in] tcpSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serialzing DISCONNECT packet.
 */
static void mqttDisconnect( int tcpSocket,
                            MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Send Ping Request to the MQTT broker.
 *
 * @param[in] tcpSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serialzing PING request packet.
 */
static void mqttKeepAlive( int tcpSocket,
                           MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Receive and validate MQTT packet from the broker, determine the type
 * of the packet and process the packet based on the type.
 *
 * @param[in] tcpSocket is a TCP socket that is connected to an MQTT broker to which
 * an MQTT connection has been established.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used to deserialize incoming MQTT packet.
 *
 */
static void mqttProcessIncomingPacket( int tcpSocket,
                                       MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Process a response or ack to an MQTT request (PING, SUBSCRIBE
 * or UNSUBSCRIBE). This function processes PING_RESP, SUB_ACK and UNSUB_ACK.
 *
 * @param[in] pIncomingPacket is a pointer to structure containing deserialized
 * MQTT response.
 * @param[in] packetId is packet identifier from the incoming MQTT packet,
 * if it was received.
 *
 * @note Not all responses contain packet identifier.
 */
static void mqttProcessResponse( MQTTPacketInfo_t * pIncomingPacket,
                                 uint16_t packetId );

/**
 * @brief Process incoming Publish message.
 *
 * @param[in] pPubInfo is a pointer to structure containing deserialized
 * Publish message.
 *
 * @param[in] packetId is packet identifier from the incoming publish if it was received.
 * valid for only for QOS1 and QOS2.
 */
static void mqttProcessIncomingPublish( MQTTPublishInfo_t * pPubInfo,
                                        uint16_t packetId );

/**
 * @brief Generate and return monotonically increasing packet identifier.
 *
 * @return The next PacketId.
 *
 * @note This function is not thread safe.
 */
static uint16_t getNextPacketIdentifier();

/**
 * @brief Calculate the interval between two timestamps, including
 * when the later value has overflowed.
 *
 * @note In C, the operands are promoted to signed integers in subtraction.
 * Using this function avoids the need to cast the result of subtractions back
 * to uint32_t.
 *
 * @param[in] later The later time stamp, in milliseconds.
 * @param[in] start The earlier time stamp, in milliseconds.
 *
 * @return later - start.
 */
static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start );

/*-----------------------------------------------------------*/

/* @brief errno to check transport error. */
extern int errno;

/* @brief Static buffer used to hold MQTT messages being sent and received. */
static uint8_t mqttSharedBuffer[ SHARED_BUFFER_SIZE ];

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted SUBSCRIBE request.
 */
static uint16_t subscribePacketIdentifier;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe response to the transmitted unsubscribe
 * request.
 */
static uint16_t unsubscribePacketIdentifier;

/*-----------------------------------------------------------*/

static uint16_t getNextPacketIdentifier()
{
    static uint16_t packetId = 0;

    packetId++;

    /* Since 0 is invalid packet identifier  value,
     * take care of it when it rolls over */
    if( packetId == 0 )
    {
        packetId = 1;
    }

    return packetId;
}

/*-----------------------------------------------------------*/

static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pTcpSocket )
{
    int status = EXIT_SUCCESS;
    struct addrinfo * pListHead = NULL, * pIndex, hint;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;
    struct timeval transportTimeout;

    /* Set up hint structure, so that only TCP address structures are returned. */
    memset( ( void * ) &hint, 0x00, sizeof( hint ) );
    hint.ai_socktype = SOCK_STREAM;
    /* Perform a DNS lookup on the given host name. */
    status = getaddrinfo( pServer, NULL, &hint, &pListHead );

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
            LogError( ( "Failed to establish TCP connection to the broker %s.\n", pServer ) );
            status = EXIT_FAILURE;
        }
        else
        {
            /* Set send and receive timeouts */
            transportTimeout.tv_sec = 0;
            transportTimeout.tv_usec = ( TRANSPORT_SEND_RECV_TIMEOUT_MS * 1000 );

            if( setsockopt( *pTcpSocket,
                            SOL_SOCKET,
                            SO_RCVTIMEO,
                            ( char * ) &transportTimeout,
                            sizeof( transportTimeout ) ) < 0 )
            {
                LogError( ( "Setting socket receive transportTimeout failed \n" ) );
                status = EXIT_FAILURE;
            }

            if( setsockopt( *pTcpSocket,
                            SOL_SOCKET,
                            SO_SNDTIMEO,
                            ( char * ) &transportTimeout,
                            sizeof( transportTimeout ) ) < 0 )
            {
                LogError( ( "Setting socket send transportTimeout failed.\n" ) );
                status = EXIT_FAILURE;
            }
        }
    }
    else
    {
        LogError( ( "DNS lookup failed for broker %s.\n", pServer ) );
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief The transport receive wrapper function supplied to the MQTT library for
 * receiving type and length of an incoming MQTT packet.
 *
 * @param[in] tcpSocket TCP socket.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToRecv Size of pBuffer.
 *
 * @return Number of bytes received or zero to indicate transportTimeout; negative value on error.
 */
static int32_t transportRecv( NetworkContext_t tcpSocket,
                              void * pBuffer,
                              size_t bytesToRecv )
{
    int32_t bytesReceived = 0;

    bytesReceived = ( int32_t ) recv( tcpSocket, pBuffer, bytesToRecv, 0 );

    if( bytesReceived == 0 )
    {
        /* Server closed the connection, treat it as an error */
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

static int createMQTTConnectionWithBroker( int tcpSocket,
                                           MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTConnectInfo_t mqttConnectInfo;
    size_t remainingLength;
    size_t packetSize;
    MQTTStatus_t result;
    MQTTPacketInfo_t incomingPacket;
    int status;
    unsigned short packetId = 0;
    bool sessionPresent = false;
    uint8_t receiveAttempts = 0;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/


    /* Many fields not used in this demo so start with everything at 0. */
    memset( ( void * ) &mqttConnectInfo, 0x00, sizeof( mqttConnectInfo ) );

    /* Start with a clean session i.e. direct the MQTT broker to discard any
     * previous session data. Also, establishing a connection with clean session
     * will ensure that the broker does not store any data when this client
     * gets disconnected. */
    mqttConnectInfo.cleanSession = true;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    mqttConnectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    mqttConnectInfo.clientIdentifierLength = ( uint16_t ) strlen( CLIENT_IDENTIFIER );

    /* Set MQTT keep-alive period. It is the responsibility of the application to ensure
     * that the interval between Control Packets being sent does not exceed the Keep Alive value.
     * In the absence of sending any other Control Packets, the Client MUST send a PINGREQ Packet. */
    mqttConnectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_PERIOD_SECONDS;

    /* Get size requirement for the connect packet */
    result = MQTT_GetConnectPacketSize( &mqttConnectInfo, NULL, &remainingLength, &packetSize );

    /* Make sure the packet size is less than static buffer size. */
    assert( result == MQTTSuccess );
    assert( packetSize < pFixedBuffer->size );

    /* Serialize MQTT connect packet into the provided buffer. */
    result = MQTT_SerializeConnect( &mqttConnectInfo, NULL, remainingLength, pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send the serialized connect packet to the MQTT broker */
    status = send( tcpSocket, ( void * ) pFixedBuffer->pBuffer, packetSize, 0 );
    assert( status == ( int ) packetSize );

    /* Reset all fields of the incoming packet structure. */
    memset( ( void * ) &incomingPacket, 0x00, sizeof( MQTTPacketInfo_t ) );

    /* Wait for connection acknowledgment.  We cannot assume received data is the
     * connection acknowledgment. Therefore this function reads type and remaining
     * length of the received packet, before processing entire packet - although in
     * this case to keep the example simple error checks are just performed by
     * asserts.
     */
    do
    {
        /* Since tcpSocket has timeout, retry until the data is available */
        result = MQTT_GetIncomingPacketTypeAndLength( transportRecv, tcpSocket, &incomingPacket );
        receiveAttempts++;
    } while ( ( result == MQTTNoDataAvailable ) && ( receiveAttempts < MQTT_MAX_RECV_ATTEMPTS ) );

    assert( result == MQTTSuccess );
    assert( incomingPacket.type == MQTT_PACKET_TYPE_CONNACK );
    assert( incomingPacket.remainingLength <= pFixedBuffer->size );

    /* Now receive the remaining packet into statically allocated buffer. */
    status = recv( tcpSocket, ( void * ) pFixedBuffer->pBuffer, incomingPacket.remainingLength, 0 );
    assert( status == ( int ) incomingPacket.remainingLength );

    incomingPacket.pRemainingData = pFixedBuffer->pBuffer;

    /* Deserialize the received packet to make sure the content of the CONNACK
     * is valid. Note that the packetId is not present in the connection ack. */
    result = MQTT_DeserializeAck( &incomingPacket, &packetId, &sessionPresent );

    if( result != MQTTSuccess )
    {
        LogError( ( "Connection with MQTT broker failed.\r\n" ) );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Successfully connected with the MQTT broker\r\n" ) );
        status = EXIT_SUCCESS;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void mqttSubscribeToTopic( int tcpSocket,
                                  MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTSubscribeInfo_t mqttSubscription[ 1 ];
    size_t remainingLength;
    size_t packetSize;
    int status;
    MQTTFixedBuffer_t fixedBuffer;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Some fields not used by this demo so start with everything as 0. */
    memset( ( void * ) &mqttSubscription, 0x00, sizeof( mqttSubscription ) );

    /* Subscribe to the MQTT_EXAMPLE_TOPIC topic filter. This example subscribes to
     * only one topic and uses QOS0. */
    mqttSubscription[ 0 ].qos = MQTTQoS0;
    mqttSubscription[ 0 ].pTopicFilter = MQTT_EXAMPLE_TOPIC;
    mqttSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( MQTT_EXAMPLE_TOPIC );

    result = MQTT_GetSubscribePacketSize( mqttSubscription,
                                          sizeof( mqttSubscription ) / sizeof( MQTTSubscribeInfo_t ),
                                          &remainingLength, &packetSize );

    /* Make sure the packet size is less than static buffer size. */
    assert( result == MQTTSuccess );
    assert( packetSize < pFixedBuffer->size );
    subscribePacketIdentifier = getNextPacketIdentifier();

    /* Serialize subscribe into statically allocated buffer. */
    result = MQTT_SerializeSubscribe( mqttSubscription,
                                      sizeof( mqttSubscription ) / sizeof( MQTTSubscribeInfo_t ),
                                      subscribePacketIdentifier,
                                      remainingLength,
                                      pFixedBuffer );

    assert( result == MQTTSuccess );

    /* Send Subscribe request to the broker. */
    status = send( tcpSocket, ( void * ) pFixedBuffer->pBuffer, packetSize, 0 );
    assert( status == ( int ) packetSize );
}
/*-----------------------------------------------------------*/

static void mqttPublishToTopic( int tcpSocket,
                                MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTPublishInfo_t mqttPublishInfo;
    size_t remainingLength;
    size_t packetSize = 0;
    size_t headerSize = 0;
    uint8_t * pPacketIdentifierHigh;
    int status;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    /* Some fields not used by this demo so start with everything as 0. */
    memset( ( void * ) &mqttPublishInfo, 0x00, sizeof( mqttPublishInfo ) );

    /* This demo uses QOS0 */
    mqttPublishInfo.qos = MQTTQoS0;
    mqttPublishInfo.retain = false;
    mqttPublishInfo.pTopicName = MQTT_EXAMPLE_TOPIC;
    mqttPublishInfo.topicNameLength = ( uint16_t ) strlen( MQTT_EXAMPLE_TOPIC );
    mqttPublishInfo.pPayload = MQTT_EXAMPLE_MESSAGE;
    mqttPublishInfo.payloadLength = strlen( MQTT_EXAMPLE_MESSAGE );

    /* Find out length of Publish packet size. */
    result = MQTT_GetPublishPacketSize( &mqttPublishInfo, &remainingLength, &packetSize );
    assert( result == MQTTSuccess );

    /* Make sure the packet size is less than static buffer size. */
    assert( packetSize < pFixedBuffer->size );

    /* Serialize MQTT Publish packet header. The publish message payload will
     * be sent directly in order to avoid copying it into the buffer.
     * QOS0 does not make use of packet identifier, therefore value of 0 is used */
    result = MQTT_SerializePublishHeader( &mqttPublishInfo,
                                          0,
                                          remainingLength,
                                          pFixedBuffer,
                                          &headerSize );
    LogDebug( ( "Serialized PUBLISH header size is %lu.",
                headerSize ) );
    assert( result == MQTTSuccess );
    /* Send Publish header to the broker. */
    status = send( tcpSocket, ( void * ) pFixedBuffer->pBuffer, headerSize, 0 );
    assert( status == ( int ) headerSize );
    /* Send Publish payload to the broker */
    status = send( tcpSocket, ( void * ) mqttPublishInfo.pPayload, mqttPublishInfo.payloadLength, 0 );
    assert( status == ( int ) mqttPublishInfo.payloadLength );
}
/*-----------------------------------------------------------*/

static void mqttUnsubscribeFromTopic( int tcpSocket,
                                      MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTSubscribeInfo_t mqttSubscription[ 1 ];
    size_t remainingLength;
    size_t packetSize;
    int status;

    /* Some fields not used by this demo so start with everything at 0. */
    memset( ( void * ) &mqttSubscription, 0x00, sizeof( mqttSubscription ) );

    /* Unsubscribe to the MQTT_EXAMPLE_TOPIC topic filter. */
    mqttSubscription[ 0 ].qos = MQTTQoS0;
    mqttSubscription[ 0 ].pTopicFilter = MQTT_EXAMPLE_TOPIC;
    mqttSubscription[ 0 ].topicFilterLength = ( uint16_t ) strlen( MQTT_EXAMPLE_TOPIC );

    result = MQTT_GetUnsubscribePacketSize( mqttSubscription,
                                            sizeof( mqttSubscription ) / sizeof( MQTTSubscribeInfo_t ),
                                            &remainingLength,
                                            &packetSize );
    assert( result == MQTTSuccess );
    /* Make sure the packet size is less than static buffer size */
    assert( packetSize < pFixedBuffer->size );

    /* Get next unique packet identifier */
    unsubscribePacketIdentifier = getNextPacketIdentifier();

    result = MQTT_SerializeUnsubscribe( mqttSubscription,
                                        sizeof( mqttSubscription ) / sizeof( MQTTSubscribeInfo_t ),
                                        unsubscribePacketIdentifier,
                                        remainingLength,
                                        pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send Unsubscribe request to the broker. */
    status = send( tcpSocket, ( void * ) pFixedBuffer->pBuffer, packetSize, 0 );
    assert( status == ( int ) packetSize );
}
/*-----------------------------------------------------------*/

static void mqttKeepAlive( int tcpSocket,
                           MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    int status;
    size_t packetSize = 0;

    /* Calculate PING request size. */
    status = MQTT_GetPingreqPacketSize( &packetSize );

    /*  Make sure the buffer can accommodate ping request. */
    assert( packetSize <= pFixedBuffer->size );

    result = MQTT_SerializePingreq( pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send Ping Request to the broker. */
    status = send( tcpSocket, ( void * ) pFixedBuffer->pBuffer, packetSize, 0 );
    assert( status == ( int ) packetSize );
}

/*-----------------------------------------------------------*/

static void mqttDisconnect( int tcpSocket,
                            MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    int32_t status;
    size_t packetSize = 0;

    status = MQTT_GetDisconnectPacketSize( &packetSize );

    assert( packetSize <= pFixedBuffer->size );

    result = MQTT_SerializeDisconnect( pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send disconnect packet to the broker */
    status = send( tcpSocket, ( void * ) pFixedBuffer->pBuffer, packetSize, 0 );
    assert( status == ( int ) packetSize );
}

/*-----------------------------------------------------------*/

static void mqttProcessResponse( MQTTPacketInfo_t * pIncomingPacket,
                                 uint16_t packetId )
{
    switch( pIncomingPacket->type & 0xf0 )
    {
        case MQTT_PACKET_TYPE_SUBACK:
            LogInfo( ( "Subscribed to the topic %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            assert( subscribePacketIdentifier == packetId );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            LogInfo( ( "Unsubscribed from the topic %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            assert( unsubscribePacketIdentifier == packetId );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            LogInfo( ( "Ping Response successfully received.\r\n" ) );
            break;

        /* Any other packet type is invalid. */
        default:
            LogWarn( ( "mqttProcessResponse() called with unknown packet type:(%u).",
                       ( unsigned ) pIncomingPacket->type ) );
    }
}

/*-----------------------------------------------------------*/

static void mqttProcessIncomingPublish( MQTTPublishInfo_t * pPubInfo,
                                        uint16_t packetId )
{
    assert( pPubInfo != NULL );

    /* Since this example does not make use of QOS1 or QOS2,
     * packet identifier is not required. */
    ( void ) packetId;

    LogInfo( ( "Incoming QOS : %d\n", pPubInfo->qos ) );

    /* Verify the received publish is for the topic we have subscribed to. */
    if( ( pPubInfo->topicNameLength == strlen( MQTT_EXAMPLE_TOPIC ) ) &&
        ( 0 == strncmp( MQTT_EXAMPLE_TOPIC, pPubInfo->pTopicName, pPubInfo->topicNameLength ) ) )
    {
        LogInfo( ( "Incoming Publish Topic Name: %.*s matches subscribed topic.\n",
                   pPubInfo->topicNameLength,
                   pPubInfo->pTopicName ) );
        LogInfo( ( "Incoming Publish Message : %.*s\n",
                   pPubInfo->payloadLength,
                   pPubInfo->pPayload ) );
    }
    else
    {
        LogError( ( "Incoming Publish Topic Name: %.*s does not match subscribed topic. \n",
                    pPubInfo->topicNameLength,
                    pPubInfo->pTopicName ) );
    }
}

/*-----------------------------------------------------------*/

static void mqttProcessIncomingPacket( int tcpSocket,
                                       MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTPacketInfo_t incomingPacket;
    MQTTPublishInfo_t publishInfo;
    uint16_t packetId = 0;
    int status;
    bool sessionPresent = false;
    uint16_t receiveAttempts = 0;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    memset( ( void * ) &incomingPacket, 0x00, sizeof( MQTTPacketInfo_t ) );

    /* Determine incoming packet type and remaining length. */
    do
    {
        /* Retry till data is available */
        result = MQTT_GetIncomingPacketTypeAndLength( transportRecv, tcpSocket, &incomingPacket );
        receiveAttempts++;
    } while ( ( result == MQTTNoDataAvailable ) && ( receiveAttempts < MQTT_MAX_RECV_ATTEMPTS ) );

    assert( result == MQTTSuccess );
    assert( incomingPacket.remainingLength <= pFixedBuffer->size );

    /* Current implementation expects an incoming Publish and three different
     * responses ( SUBACK, PINGRESP and UNSUBACK ). */

    /* Receive the remaining bytes. */
    status = recv( tcpSocket, ( void * ) pFixedBuffer->pBuffer, incomingPacket.remainingLength, 0 );
    assert( status == ( int ) incomingPacket.remainingLength );

    incomingPacket.pRemainingData = pFixedBuffer->pBuffer;

    if( ( incomingPacket.type & 0xf0 ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        result = MQTT_DeserializePublish( &incomingPacket, &packetId, &publishInfo );
        assert( result == MQTTSuccess );

        /* Process incoming Publish message. */
        mqttProcessIncomingPublish( &publishInfo, packetId );
    }
    else
    {
        /* If the received packet is not a Publish message, then it is an ACK for one
         * of the messages we sent out, verify that the ACK packet is a valid MQTT
         * packet. Since CONNACK is already processed, session present parameter is
         * to NULL */
        result = MQTT_DeserializeAck( &incomingPacket, &packetId, &sessionPresent );
        assert( result == MQTTSuccess );

        /* Process the response. */
        mqttProcessResponse( &incomingPacket, packetId );
    }
}

/*-----------------------------------------------------------*/

static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start )
{
    return later - start;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 */
int main( int argc,
          char ** argv )
{
    int status = EXIT_SUCCESS;
    MQTTFixedBuffer_t fixedBuffer;
    uint16_t loopCount = 0;
    const uint16_t maxLoopCount = 5U;
    uint16_t demoIterations = 0;
    const uint16_t maxDemoIterations = 10U;
    time_t lastControlPacketSentTimeStamp = 0;
    struct timespec currentTimeStamp;
    uint32_t timeDiff = 0;
    bool controlPacketSent = false;
    bool publishPacketSent = false;
    int tcpSocket = -1;

    /***
     * Set Fixed size buffer structure that is required by API to serialize
     * and deserialize data. pBuffer is pointing to a fixed sized mqttSharedBuffer.
     * The application may allocate dynamic memory as well.
     ***/
    fixedBuffer.pBuffer = mqttSharedBuffer;
    fixedBuffer.size = SHARED_BUFFER_SIZE;

    for( demoIterations = 0; demoIterations < maxDemoIterations; demoIterations++ )
    {
        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in MQTT_BROKER_ENDPOINT and
         * MQTT_BROKER_PORT at the top of this file. */
        LogInfo( ( "Establishing TCP connection to the broker  %s.\r\n", MQTT_BROKER_ENDPOINT ) );
        status = connectToServer( MQTT_BROKER_ENDPOINT, MQTT_BROKER_PORT, &tcpSocket );

        if( status == EXIT_SUCCESS )
        {
            /* Sends an MQTT Connect packet over the already connected TCP socket
             * tcpSocket, and waits for connection acknowledgment (CONNACK) packet. */
            LogInfo( ( "Establishing MQTT connection to the broker  %s.\r\n", MQTT_BROKER_ENDPOINT ) );
            status = createMQTTConnectionWithBroker( tcpSocket, &fixedBuffer );
            assert( status == EXIT_SUCCESS );

            /**************************** Subscribe. ******************************/

            /* The client is now connected to the broker. Subscribe to the topic
             * as specified in MQTT_EXAMPLE_TOPIC at the top of this file by sending a
             * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
             * This client will then publish to the same topic it subscribed to, so it
             * will expect all the messages it sends to the broker to be sent back to it
             * from the broker. This demo uses QOS0 in subscribe, therefore, the Publish
             * messages received from the broker will have QOS0. */
            /* Subscribe and SUBACK */
            LogInfo( ( "Attempt to subscribe to the MQTT topic %s\r\n", MQTT_EXAMPLE_TOPIC ) );
            mqttSubscribeToTopic( tcpSocket, &fixedBuffer );

            /* Since subscribe is a control packet, record the last control packet sent
             * timestamp. This timestamp will be used to determine if it is necessary to
             * send a PINGREQ packet. */
            status = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );
            assert( status == 0 );
            lastControlPacketSentTimeStamp = currentTimeStamp.tv_sec;

            /* Process incoming packet from the broker. After sending the subscribe, the
             * client may receive a publish before it receives a subscribe ack. Therefore,
             * call generic incoming packet processing function. Since this demo is
             * subscribing to the topic to which no one is publishing, probability of
             * receiving Publish message before subscribe ack is zero; but application
             * must be ready to receive any packet.  This demo uses the generic packet
             * processing function everywhere to highlight this fact. */
            mqttProcessIncomingPacket( tcpSocket, &fixedBuffer );

            /********************* Publish and Keep Alive Loop. ********************/
            /* Publish messages with QOS0, send and process Keep alive messages. */
            for( loopCount = 0; loopCount < maxLoopCount; loopCount++ )
            {
                /* Get the current time stamp */
                status = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );

                /* Publish to the topic every other time to trigger sending of PINGREQ  */
                if( publishPacketSent == false )
                {
                    LogInfo( ( "Publish to the MQTT topic %s\r\n", MQTT_EXAMPLE_TOPIC ) );
                    mqttPublishToTopic( tcpSocket, &fixedBuffer );

                    /* Set control packet sent flag to true so that the lastControlPacketSent
                     * timestamp will be updated. */
                    controlPacketSent = true;
                    publishPacketSent = true;
                }
                else
                {
                    /* Check if the keep-alive period has elapsed, since the last control packet was sent.
                     * If the period has elapsed, send out MQTT PINGREQ to the broker.  */
                    timeDiff = calculateElapsedTime( currentTimeStamp.tv_sec, lastControlPacketSentTimeStamp );
                    LogInfo( ( "Time Since last control packet %u \r\n", timeDiff ) );

                    if( timeDiff >= MQTT_KEEP_ALIVE_PERIOD_SECONDS )
                    {
                        /* Send PINGREQ to the broker */
                        LogInfo( ( "Sending PINGREQ to the broker\n " ) );
                        mqttKeepAlive( tcpSocket, &fixedBuffer );
                        controlPacketSent = true;
                    }

                    /* Since PUBLISH packet is not sent for this iteration, set publishPacketSent to false
                     * so the next iteration will send PUBLISH .*/
                    publishPacketSent = false;
                }

                if( controlPacketSent == true )
                {
                    /* Reset the last control packet sent timestamp */
                    status = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );
                    assert( status == 0 );
                    lastControlPacketSentTimeStamp = currentTimeStamp.tv_sec;
                    controlPacketSent = false;

                    /* Since the application is subscribed publishing messages to the same topic,
                     * the broker will send the same message back to the application.
                     * Process incoming PUBLISH echo or PINGRESP. */
                    mqttProcessIncomingPacket( tcpSocket, &fixedBuffer );
                }

                /* Sleep until keep alive time period, so that for the next iteration this
                 * loop will send out a PINGREQ if PUBLISH was not sent for this iteration.
                 * The broker will wait till 1.5 times keep-alive period before it disconnects
                 * the client. */
                ( void ) sleep( MQTT_KEEP_ALIVE_PERIOD_SECONDS );
            }

            /* Unsubscribe from the previously subscribed topic */
            LogInfo( ( "Unsubscribe from the MQTT topic %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            mqttUnsubscribeFromTopic( tcpSocket, &fixedBuffer );
            /* Process Incoming unsubscribe ack from the broker. */
            mqttProcessIncomingPacket( tcpSocket, &fixedBuffer );

            /* Send an MQTT Disconnect packet over the already connected TCP socket.
             * There is no corresponding response for the disconnect packet. After sending
             * disconnect, client must close the network connection. */
            LogInfo( ( "Disconnecting the MQTT connection with %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            mqttDisconnect( tcpSocket, &fixedBuffer );

            /* Close the TCP connection. */
            ( void ) shutdown( tcpSocket, SHUT_RDWR );
            ( void ) close( tcpSocket );
        }

        if( demoIterations < ( maxDemoIterations - 1U ) )
        {
            /* Wait for some time between two iterations to ensure that we do not
             * bombard the public test mosquitto broker. */
            LogInfo( ( "Short delay before starting the next iteration.... \r\n\r\n" ) );
            ( void ) sleep( MQTT_DEMO_ITERATION_DELAY_SECONDS );
        }
    }

    LogInfo( ( "Demo completed successfully.\r\n" ) );
    return status;
}

/*-----------------------------------------------------------*/
