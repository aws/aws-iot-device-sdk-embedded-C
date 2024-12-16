/*
 * AWS IoT Device SDK for Embedded C 202412.00
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

/**
 * @brief Demo that shows use of the MQTT serializer / deserializer API
 * to build an ultra-light weight MQTT client. This shows that a lighter weight
 * MQTT client can be developed without using the higher-level
 * MQTT API of core_mqtt.h, but just the serializer / deserializer API.
 * The core_mqtt_serializer.h API lets user to serialize and
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
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* POSIX includes. */
#include <unistd.h>

/* MQTT Serializer Serializer API header. */
#include "core_mqtt_serializer.h"

/* Plaintext transport implementation. */
#include "plaintext_posix.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/*Include clock header for millisecond sleep function. */
#include "clock.h"

/* Check that the broker endpoint is defined. */
#ifndef BROKER_ENDPOINT
    #error "Please define an MQTT broker endpoint, BROKER_ENDPOINT, in demo_config.h."
#endif

/* Check that client identifier is defined. */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH                   ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

/**
 * @brief The topic to subscribe and publish to in the example.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define MQTT_EXAMPLE_TOPIC                       CLIENT_IDENTIFIER "/example/topic"

/**
 * @brief Length of client MQTT topic.
 */
#define MQTT_EXAMPLE_TOPIC_LENGTH                ( ( uint16_t ) ( sizeof( MQTT_EXAMPLE_TOPIC ) - 1 ) )

/**
 * @brief Size of the network buffer for MQTT packets.
 */
#ifndef NETWORK_BUFFER_SIZE
    #define NETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief The MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE                 "Hello World!"

/**
 * @brief Keep alive period in seconds for MQTT connection.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS     ( 5U )

/**
 * @brief Socket layer transportTimeout in milliseconds.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS       ( 1000U )

/**
 * @brief Number of time network receive will be attempted
 * if it fails due to transportTimeout.
 */
#define MQTT_MAX_RECV_ATTEMPTS               ( 1000U )

/**
 * @brief Time to wait in milliseconds before attempting to obtain
 * an MQTT packet in response to a previously sent message.
 */
#define MQTT_RESPONSE_WAIT_TIME_MS           ( 50U )

/**
 * @brief Delay between two demo iterations.
 */
#define MQTT_DEMO_ITERATION_DELAY_SECONDS    ( 5U )

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    PlaintextParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber();

/**
 * @brief Connect to MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increase until until maximum reconnection
 * backoff time is reached or the number of attempts are exhausted.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing CONNECT packet and deserializing CONN-ACK.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext,
                                              MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Establish an MQTT session over a TCP connection by sending MQTT CONNECT.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing CONNECT packet and deserializing CONN-ACK.
 *
 * @return EXIT_SUCCESS if an MQTT session is established; EXIT_FAILURE otherwise.
 */
static int createMQTTConnectionWithBroker( NetworkContext_t * pNetworkContext,
                                           MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Subscribes to the topic as specified in MQTT_EXAMPLE_TOPIC at the top of
 * this file.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing SUBSCRIBE packet.
 *
 */
static void mqttSubscribeToTopic( NetworkContext_t * pNetworkContext,
                                  MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief  Publishes a message MQTT_EXAMPLE_MESSAGE on MQTT_EXAMPLE_TOPIC topic.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing PUBLISH packet.
 *
 */
static void mqttPublishToTopic( NetworkContext_t * pNetworkContext,
                                MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Unsubscribes from the previously subscribed topic as specified
 * in MQTT_EXAMPLE_TOPIC.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing UNSUBSCRIBE packet.
 *
 */
static void mqttUnsubscribeFromTopic( NetworkContext_t * pNetworkContext,
                                      MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Disconnect From the MQTT broker.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing DISCONNECT packet.
 */
static void mqttDisconnect( NetworkContext_t * pNetworkContext,
                            MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Send Ping Request to the MQTT broker.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used for serializing PING request packet.
 */
static void mqttKeepAlive( NetworkContext_t * pNetworkContext,
                           MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Receive and validate MQTT packet from the broker, determine the type
 * of the packet and process the packet based on the type.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 * @param[in] pFixedBuffer Pointer to a structure containing fixed buffer and its length.
 * The buffer is used to deserialize incoming MQTT packet.
 *
 */
static void mqttProcessIncomingPacket( NetworkContext_t * pNetworkContext,
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
static uint16_t getNextPacketIdentifier( void );

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

/**
 * @brief Static buffer used to hold MQTT messages being sent and received.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

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

/**
 * @brief Status of latest Subscribe ACK;
 * it is updated every time a Subscribe ACK is processed.
 */
static bool globalSubAckStatus = false;

/*-----------------------------------------------------------*/

static uint16_t getNextPacketIdentifier( void )
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

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext,
                                              MQTTFixedBuffer_t * pFixedBuffer )
{
    int returnStatus = EXIT_FAILURE;
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;
    BackoffAlgorithmContext_t reconnectParams;
    ServerInfo_t serverInfo;
    uint16_t nextRetryBackOff = 0U;
    struct timespec tp;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = BROKER_ENDPOINT;
    serverInfo.hostNameLength = BROKER_ENDPOINT_LENGTH;
    serverInfo.port = BROKER_PORT;

    /* Seed pseudo random number generator used in the demo for
     * backoff period calculation when retrying failed network operations
     * with broker. */

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );
    /* Seed pseudo random number generator with nanoseconds. */
    srand( tp.tv_nsec );

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &reconnectParams,
                                       CONNECTION_RETRY_BACKOFF_BASE_MS,
                                       CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       CONNECTION_RETRY_MAX_ATTEMPTS );

    /* Attempt to connect to MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase till maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TCP connection with the MQTT broker. This example connects
         * to the MQTT broker as specified in BROKER_ENDPOINT and BROKER_PORT
         * at the demo config header. */
        LogInfo( ( "Creating a TCP connection to %.*s:%d.",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT,
                   BROKER_PORT ) );
        socketStatus = Plaintext_Connect( pNetworkContext,
                                          &serverInfo,
                                          TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                          TRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( socketStatus == SOCKETS_SUCCESS )
        {
            /* Sends an MQTT Connect packet over the already connected TCP socket
             * and waits for connection acknowledgment (CONNACK) packet. */
            LogInfo( ( "Establishing MQTT connection to the broker  %s.\r\n", BROKER_ENDPOINT ) );
            returnStatus = createMQTTConnectionWithBroker( pNetworkContext, pFixedBuffer );

            if( returnStatus == EXIT_FAILURE )
            {
                /* Close the TCP connection.  */
                ( void ) Plaintext_Disconnect( pNetworkContext );
            }
        }

        if( returnStatus == EXIT_FAILURE )
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &reconnectParams, generateRandomNumber(), &nextRetryBackOff );

            if( backoffAlgStatus == BackoffAlgorithmRetriesExhausted )
            {
                LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
                returnStatus = EXIT_FAILURE;
            }
            else if( backoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. Retrying connection "
                           "after %hu ms backoff.",
                           ( unsigned short ) nextRetryBackOff ) );
                Clock_SleepMs( nextRetryBackOff );
            }
        }
    } while( ( returnStatus == EXIT_FAILURE ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int createMQTTConnectionWithBroker( NetworkContext_t * pNetworkContext,
                                           MQTTFixedBuffer_t * pFixedBuffer )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTConnectInfo_t mqttConnectInfo;
    size_t remainingLength;
    size_t packetSize;
    MQTTStatus_t result;
    MQTTPacketInfo_t incomingPacket;
    unsigned short packetId = 0;
    bool sessionPresent = false;

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
    mqttConnectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

    /* Get size requirement for the connect packet */
    result = MQTT_GetConnectPacketSize( &mqttConnectInfo, NULL, &remainingLength, &packetSize );

    /* Make sure the packet size is less than static buffer size. */
    assert( result == MQTTSuccess );
    assert( packetSize < pFixedBuffer->size );

    /* Serialize MQTT connect packet into the provided buffer. */
    result = MQTT_SerializeConnect( &mqttConnectInfo, NULL, remainingLength, pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send the serialized connect packet to the MQTT broker */
    returnStatus = Plaintext_Send( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, packetSize );
    assert( returnStatus == ( int ) packetSize );

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
        /* Wait a bit before attempting to receive an incoming response to allow
         * time for the server to respond. */
        Clock_SleepMs( MQTT_RESPONSE_WAIT_TIME_MS );
        /* Since TCP socket has timeout, retry until the data is available */
        result = MQTT_GetIncomingPacketTypeAndLength( Plaintext_Recv, pNetworkContext, &incomingPacket );
        LogInfo( ( "MQTT_GetIncomingPacketTypeAndLength returned: %d\n", result ) );
    } while( ( result == MQTTNoDataAvailable ) );

    assert( result == MQTTSuccess );
    assert( incomingPacket.type == MQTT_PACKET_TYPE_CONNACK );
    assert( incomingPacket.remainingLength <= pFixedBuffer->size );

    /* Now receive the remaining packet into statically allocated buffer. */
    returnStatus = Plaintext_Recv( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, incomingPacket.remainingLength );
    assert( returnStatus == ( int ) incomingPacket.remainingLength );

    incomingPacket.pRemainingData = pFixedBuffer->pBuffer;

    /* Deserialize the received packet to make sure the content of the CONNACK
     * is valid. Note that the packetId is not present in the connection ack. */
    result = MQTT_DeserializeAck( &incomingPacket, &packetId, &sessionPresent );

    if( result != MQTTSuccess )
    {
        LogError( ( "Connection with MQTT broker failed.\r\n" ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Successfully connected with the MQTT broker\r\n" ) );
        returnStatus = EXIT_SUCCESS;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static void mqttSubscribeToTopic( NetworkContext_t * pNetworkContext,
                                  MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTSubscribeInfo_t mqttSubscription[ 1 ];
    size_t remainingLength;
    size_t packetSize;
    int status;

    /* Suppress unused variable warnings when asserts are disabled in build. */
    ( void ) status;
    ( void ) result;

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
    status = Plaintext_Send( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, packetSize );
    assert( status == ( int ) packetSize );
}
/*-----------------------------------------------------------*/

static void mqttPublishToTopic( NetworkContext_t * pNetworkContext,
                                MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTPublishInfo_t mqttPublishInfo;
    size_t remainingLength;
    size_t packetSize = 0;
    size_t headerSize = 0;
    int status;

    /* Suppress unused variable warnings when asserts are disabled in build. */
    ( void ) status;
    ( void ) result;

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
                ( unsigned long ) headerSize ) );
    assert( result == MQTTSuccess );
    /* Send Publish header to the broker. */
    status = Plaintext_Send( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, headerSize );
    assert( status == ( int ) headerSize );
    /* Send Publish payload to the broker */
    status = Plaintext_Send( pNetworkContext, ( void * ) mqttPublishInfo.pPayload, mqttPublishInfo.payloadLength );
    assert( status == ( int ) mqttPublishInfo.payloadLength );
}
/*-----------------------------------------------------------*/

static void mqttUnsubscribeFromTopic( NetworkContext_t * pNetworkContext,
                                      MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTSubscribeInfo_t mqttSubscription[ 1 ];
    size_t remainingLength;
    size_t packetSize;
    int status;

    /* Suppress unused variable warnings when asserts are disabled in build. */
    ( void ) status;
    ( void ) result;

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
    status = Plaintext_Send( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, packetSize );
    assert( status == ( int ) packetSize );
}
/*-----------------------------------------------------------*/

static void mqttKeepAlive( NetworkContext_t * pNetworkContext,
                           MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    int status;
    size_t packetSize = 0;

    /* Suppress unused variable warnings when asserts are disabled in build. */
    ( void ) status;
    ( void ) result;

    /* Calculate PING request size. */
    status = MQTT_GetPingreqPacketSize( &packetSize );

    /*  Make sure the buffer can accommodate ping request. */
    assert( packetSize <= pFixedBuffer->size );

    result = MQTT_SerializePingreq( pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send Ping Request to the broker. */
    status = Plaintext_Send( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, packetSize );
    assert( status == ( int ) packetSize );
}

/*-----------------------------------------------------------*/

static void mqttDisconnect( NetworkContext_t * pNetworkContext,
                            MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    int32_t status;
    size_t packetSize = 0;

    /* Suppress unused variable warnings when asserts are disabled in build. */
    ( void ) status;
    ( void ) result;

    status = MQTT_GetDisconnectPacketSize( &packetSize );

    assert( packetSize <= pFixedBuffer->size );

    result = MQTT_SerializeDisconnect( pFixedBuffer );
    assert( result == MQTTSuccess );

    /* Send disconnect packet to the broker */
    status = Plaintext_Send( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, packetSize );
    assert( status == ( int ) packetSize );
}

/*-----------------------------------------------------------*/

static void mqttProcessResponse( MQTTPacketInfo_t * pIncomingPacket,
                                 uint16_t packetId )
{
    /* Suppress unused parameter warnings when asserts are disabled in build. */
    ( void ) packetId;

    switch( pIncomingPacket->type & 0xf0 )
    {
        case MQTT_PACKET_TYPE_SUBACK:

            /* Check if recent subscription request has been accepted. globalSubAckStatus is updated
             * in mqttProcessIncomingPacket to reflect the status of the SUBACK sent by the broker. */
            if( globalSubAckStatus == true )
            {
                LogInfo( ( "Subscribed to the topic %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            }
            else
            {
                LogInfo( ( "Server refused subscription request for the topic %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            }

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
                                        uint16_t packetIdentifier )
{
    assert( pPubInfo != NULL );

    /* Since this example does not make use of QOS1 or QOS2,
     * packet identifier is not required. */
    ( void ) packetIdentifier;

    LogInfo( ( "Incoming QOS : %d\n", pPubInfo->qos ) );

    /* Verify the received publish is for the topic we have subscribed to. */
    if( ( pPubInfo->topicNameLength == MQTT_EXAMPLE_TOPIC_LENGTH ) &&
        ( 0 == strncmp( MQTT_EXAMPLE_TOPIC, pPubInfo->pTopicName, pPubInfo->topicNameLength ) ) )
    {
        LogInfo( ( "Incoming Publish Topic Name: %.*s matches subscribed topic.\n"
                   "Incoming Publish message Packet ID is %u.\n"
                   "Incoming Publish Message : %.*s.\n\n",
                   pPubInfo->topicNameLength,
                   pPubInfo->pTopicName,
                   packetIdentifier,
                   ( int ) pPubInfo->payloadLength,
                   ( const char * ) pPubInfo->pPayload ) );
    }
    else
    {
        LogError( ( "Incoming Publish Topic Name: %.*s does not match subscribed topic. \n",
                    pPubInfo->topicNameLength,
                    pPubInfo->pTopicName ) );
    }
}

/*-----------------------------------------------------------*/

static void mqttProcessIncomingPacket( NetworkContext_t * pNetworkContext,
                                       MQTTFixedBuffer_t * pFixedBuffer )
{
    MQTTStatus_t result;
    MQTTPacketInfo_t incomingPacket;
    MQTTPublishInfo_t publishInfo;
    uint16_t packetId = 0;
    int status;
    bool sessionPresent = false;

    /* Suppress unused variable warning when asserts are disabled in build. */
    ( void ) status;

    /***
     * For readability, error handling in this function is restricted to the use of
     * asserts().
     ***/

    memset( ( void * ) &incomingPacket, 0x00, sizeof( MQTTPacketInfo_t ) );

    /* Determine incoming packet type and remaining length. */
    do
    {
        /* Wait a bit before attempting to receive an incoming response to allow
         * time for the server to respond. */
        Clock_SleepMs( MQTT_RESPONSE_WAIT_TIME_MS );
        /* Retry till data is available */
        result = MQTT_GetIncomingPacketTypeAndLength( Plaintext_Recv, pNetworkContext, &incomingPacket );
        LogInfo( ( "MQTT_GetIncomingPacketTypeAndLength returned: %d\n", result ) );
    } while( ( result == MQTTNoDataAvailable ) );

    assert( result == MQTTSuccess );
    assert( incomingPacket.remainingLength <= pFixedBuffer->size );

    /* Current implementation expects an incoming Publish and three different
     * responses ( SUBACK, PINGRESP and UNSUBACK ). */

    /* Transport read is required only if remaining length is greater than 0.
     * Remaining length for PINGRESP will be 0. */
    if( incomingPacket.remainingLength > 0 )
    {
        /* Receive the remaining bytes. */
        status = Plaintext_Recv( pNetworkContext, ( void * ) pFixedBuffer->pBuffer, incomingPacket.remainingLength );
        assert( status == ( int ) incomingPacket.remainingLength );
    }

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

        if( incomingPacket.type == MQTT_PACKET_TYPE_SUBACK )
        {
            globalSubAckStatus = ( result == MQTTSuccess );
            assert( result == MQTTSuccess || result == MQTTServerRefused );
        }
        else
        {
            assert( result == MQTTSuccess );
        }

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
    int returnStatus = EXIT_SUCCESS;
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
    NetworkContext_t networkContext = { 0 };
    PlaintextParams_t plaintextParams = { 0 };
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    BackoffAlgorithmContext_t retryParams;
    uint16_t nextRetryBackOff = 0U;

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &plaintextParams;

    /***
     * Set Fixed size buffer structure that is required by API to serialize
     * and deserialize data. pBuffer is pointing to a fixed sized buffer.
     * The application may allocate dynamic memory as well.
     ***/
    fixedBuffer.pBuffer = buffer;
    fixedBuffer.size = NETWORK_BUFFER_SIZE;

    for( demoIterations = 0; demoIterations < maxDemoIterations; demoIterations++ )
    {
        /* Establish a TCP connection with the MQTT broker. This example connects to
         * the MQTT broker as specified in BROKER_ENDPOINT and BROKER_PORT
         * at the demo config header. */
        LogInfo( ( "Establishing TCP connection to the broker  %s.\r\n", BROKER_ENDPOINT ) );
        returnStatus = connectToServerWithBackoffRetries( &networkContext, &fixedBuffer );

        if( returnStatus == EXIT_SUCCESS )
        {
            /**************************** Subscribe, Re-subscribe, and Keep-Alive ******************************/

            /* Initialize retry attempts and interval. */
            BackoffAlgorithm_InitializeParams( &retryParams,
                                               CONNECTION_RETRY_BACKOFF_BASE_MS,
                                               CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                               CONNECTION_RETRY_MAX_ATTEMPTS );

            do
            {
                /* The client is now connected to the broker. Subscribe to the topic
                 * as specified in MQTT_EXAMPLE_TOPIC at the top of this file by sending a
                 * subscribe packet then waiting for a subscribe acknowledgment (SUBACK).
                 * This client will then publish to the same topic it subscribed to, so it
                 * will expect all the messages it sends to the broker to be sent back to it
                 * from the broker. This demo uses QOS0 in subscribe, therefore, the Publish
                 * messages received from the broker will have QOS0. */
                /* Subscribe and SUBACK */
                LogInfo( ( "Attempt to subscribe to the MQTT topic %s\r\n", MQTT_EXAMPLE_TOPIC ) );
                mqttSubscribeToTopic( &networkContext, &fixedBuffer );

                /* Since subscribe is a control packet, record the last control packet sent
                 * timestamp. This timestamp will be used to determine if it is necessary to
                 * send a PINGREQ packet. */
                returnStatus = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );
                assert( returnStatus == 0 );
                lastControlPacketSentTimeStamp = currentTimeStamp.tv_sec;

                /* Process incoming packet from the broker. After sending the subscribe, the
                 * client may receive a publish before it receives a subscribe ack. Therefore,
                 * call generic incoming packet processing function. Since this demo is
                 * subscribing to the topic to which no one is publishing, probability of
                 * receiving Publish message before subscribe ack is zero; but application
                 * must be ready to receive any packet.  This demo uses the generic packet
                 * processing function everywhere to highlight this fact. */
                mqttProcessIncomingPacket( &networkContext, &fixedBuffer );

                /* Check status of suback sent from broker. If server rejected the subscription
                 * request, attempt resubscription to the topic filter. */
                if( globalSubAckStatus == false )
                {
                    /* Send PINGREQ to the broker. A PINGREQ is sent to avoid hitting keep-alive
                     * time-out period during backoff and sleep execution, before the next
                     * subscription attempt. */
                    LogInfo( ( "Sending PINGREQ to the broker\n " ) );
                    mqttKeepAlive( &networkContext, &fixedBuffer );

                    /* Reset the last control packet sent timestamp, after sending control packet
                     * PINGREQ. This timestamp will be used to determine if it is necessary to
                     * send another PINGREQ packet. */
                    returnStatus = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );
                    assert( returnStatus == 0 );
                    lastControlPacketSentTimeStamp = currentTimeStamp.tv_sec;

                    /* Process incoming PINGRESP from the broker */
                    mqttProcessIncomingPacket( &networkContext, &fixedBuffer );

                    /* Generate a random number and get back-off value (in milliseconds) for the next re-subscribe attempt. */
                    backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &retryParams, generateRandomNumber(), &nextRetryBackOff );

                    if( backoffAlgStatus == BackoffAlgorithmRetriesExhausted )
                    {
                        LogError( ( "Subscription to topic failed, all attempts exhausted." ) );
                    }
                    else if( backoffAlgStatus == BackoffAlgorithmSuccess )
                    {
                        LogWarn( ( "Server rejected subscription request. "
                                   "Retrying connection after %hu ms backoff.",
                                   ( unsigned short ) nextRetryBackOff ) );
                        Clock_SleepMs( nextRetryBackOff );
                    }
                }
            } while( ( globalSubAckStatus == false ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

            assert( globalSubAckStatus == true );

            /********************* Publish and Keep Alive Loop. ********************/
            /* Publish messages with QOS0, send and process Keep alive messages. */
            for( loopCount = 0; loopCount < maxLoopCount; loopCount++ )
            {
                /* Get the current time stamp */
                returnStatus = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );

                /* Publish to the topic every other time to trigger sending of PINGREQ  */
                if( publishPacketSent == false )
                {
                    LogInfo( ( "Publish to the MQTT topic %s\r\n", MQTT_EXAMPLE_TOPIC ) );
                    mqttPublishToTopic( &networkContext, &fixedBuffer );

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
                    LogInfo( ( "Time since last control packet %u \r\n", timeDiff ) );

                    if( timeDiff >= MQTT_KEEP_ALIVE_INTERVAL_SECONDS )
                    {
                        /* Send PINGREQ to the broker */
                        LogInfo( ( "Sending PINGREQ to the broker\n " ) );
                        mqttKeepAlive( &networkContext, &fixedBuffer );
                        controlPacketSent = true;
                    }

                    /* Since PUBLISH packet is not sent for this iteration, set publishPacketSent to false
                     * so the next iteration will send PUBLISH .*/
                    publishPacketSent = false;
                }

                if( controlPacketSent == true )
                {
                    /* Reset the last control packet sent timestamp */
                    returnStatus = clock_gettime( CLOCK_MONOTONIC, &currentTimeStamp );
                    assert( returnStatus == 0 );
                    lastControlPacketSentTimeStamp = currentTimeStamp.tv_sec;
                    controlPacketSent = false;

                    /* Since the application is subscribed publishing messages to the same topic,
                     * the broker will send the same message back to the application.
                     * Process incoming PUBLISH echo or PINGRESP. */
                    mqttProcessIncomingPacket( &networkContext, &fixedBuffer );
                }

                /* Sleep until keep alive time period, so that for the next iteration this
                 * loop will send out a PINGREQ if PUBLISH was not sent for this iteration.
                 * The broker will wait till 1.5 times keep-alive period before it disconnects
                 * the client. */
                ( void ) sleep( MQTT_KEEP_ALIVE_INTERVAL_SECONDS );
            }

            /* Unsubscribe from the previously subscribed topic */
            LogInfo( ( "Unsubscribe from the MQTT topic %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            mqttUnsubscribeFromTopic( &networkContext, &fixedBuffer );
            /* Process Incoming unsubscribe ack from the broker. */
            mqttProcessIncomingPacket( &networkContext, &fixedBuffer );

            /* Reset global SUBACK status variable after completion of subscription request cycle. */
            globalSubAckStatus = false;

            /* Send an MQTT Disconnect packet over the already connected TCP socket.
             * There is no corresponding response for the disconnect packet. After sending
             * disconnect, client must close the network connection. */
            LogInfo( ( "Disconnecting the MQTT connection with %s.\r\n", MQTT_EXAMPLE_TOPIC ) );
            mqttDisconnect( &networkContext, &fixedBuffer );

            /* Close the TCP connection.  */
            ( void ) Plaintext_Disconnect( &networkContext );
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
    return returnStatus;
}

/*-----------------------------------------------------------*/
