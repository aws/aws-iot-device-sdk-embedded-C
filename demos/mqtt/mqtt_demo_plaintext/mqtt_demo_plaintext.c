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

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* MQTT API header. */
#include "mqtt.h"

/* Plaintext sockets transport implementation. */
#include "plaintext_posix.h"

/* Reconnect parameters. */
#include "transport_reconnect.h"

/* Clock for timer. */
#include "clock.h"

/**
 * These configuration settings are required to run the plaintext demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * Provide default values for undefined configuration settings.
 */
#ifndef BROKER_PORT
    #define BROKER_PORT    ( 1883 )
#endif

#ifndef NETWORK_BUFFER_SIZE
    #define NETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH            ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH              ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS             ( 1000U )

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
 * @brief The length of the MQTT message published in this example.
 */
#define MQTT_EXAMPLE_MESSAGE_LENGTH         ( ( uint16_t ) ( sizeof( MQTT_EXAMPLE_MESSAGE ) - 1 ) )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 500U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the Client to ensure that the interval between
 *  Control Packets being sent does not exceed the this Keep Alive value. In the
 *  absence of sending any other Control Packets, the Client MUST send a
 *  PINGREQ Packet.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS    ( 60U )

/**
 * @brief Delay between MQTT publishes in seconds.
 */
#define DELAY_BETWEEN_PUBLISHES_SECONDS     ( 1U )

/**
 * @brief Number of PUBLISH messages sent per iteration.
 */
#define MQTT_PUBLISH_COUNT_PER_LOOP         ( 5U )

/**
 * @brief Delay in seconds between two iterations of subscribePublishLoop().
 */
#define MQTT_SUBPUB_LOOP_DELAY_SECONDS      ( 5U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 20 )

/*-----------------------------------------------------------*/

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted subscribe.
 */
static uint16_t globalSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe ACK to the transmitted unsubscribe
 * request.
 */
static uint16_t globalUnsubscribePacketIdentifier = 0U;

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/*-----------------------------------------------------------*/

/**
 * @brief Connect to MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increased till maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext );

/**
 * @brief A function that connects to MQTT broker,
 * subscribes a topic, publishes to the same
 * topic MQTT_PUBLISH_COUNT_PER_LOOP number of times, and verifies if it
 * receives the Publish message back.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int subscribePublishLoop( NetworkContext_t * pNetworkContext );

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
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pNetworkContext Pointer to the network context created using Plaintext_Connect.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext );

/**
 * @brief Close an MQTT session by sending MQTT DISCONNECT.
 *
 * @param[in] pMqttContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if DISCONNECT was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int disconnectMqttSession( MQTTContext_t * pMqttContext );

/**
 * @brief Sends an MQTT SUBSCRIBE to subscribe to #MQTT_EXAMPLE_TOPIC
 * defined at the top of the file.
 *
 * @param[in] pMqttContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if SUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int subscribeToTopic( MQTTContext_t * pMqttContext );

/**
 * @brief Sends an MQTT UNSUBSCRIBE to unsubscribe from
 * #MQTT_EXAMPLE_TOPIC defined at the top of the file.
 *
 * @param[in] pMqttContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if UNSUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int unsubscribeFromTopic( MQTTContext_t * pMqttContext );

/**
 * @brief Sends an MQTT PUBLISH to #MQTT_EXAMPLE_TOPIC defined at
 * the top of the file.
 *
 * @param[in] pMqttContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if PUBLISH was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int publishToTopic( MQTTContext_t * pMqttContext );

/*-----------------------------------------------------------*/

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool retriesArePending = true;
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;
    TransportReconnectParams_t reconnectParams;
    ServerInfo_t serverInfo;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = BROKER_ENDPOINT;
    serverInfo.hostNameLength = BROKER_ENDPOINT_LENGTH;
    serverInfo.port = BROKER_PORT;

    /* Initialize reconnect attempts and interval */
    Transport_ReconnectParamsReset( &reconnectParams );

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

        if( socketStatus != SOCKETS_SUCCESS )
        {
            LogWarn( ( "Connection to the broker failed. Retrying connection with backoff and jitter." ) );
            retriesArePending = Transport_ReconnectBackoffAndSleep( &reconnectParams );
        }

        if( retriesArePending == false )
        {
            LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            returnStatus = EXIT_FAILURE;
        }
    } while( ( socketStatus != SOCKETS_SUCCESS ) && ( retriesArePending == true ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo,
                                   uint16_t packetIdentifier )
{
    assert( pPublishInfo != NULL );

    ( void ) packetIdentifier;

    /* Process incoming Publish. */
    LogInfo( ( "Incoming QOS : %d.", pPublishInfo->qos ) );

    /* Verify the received publish is for the topic we have subscribed to. */
    if( ( pPublishInfo->topicNameLength == MQTT_EXAMPLE_TOPIC_LENGTH ) &&
        ( 0 == strncmp( MQTT_EXAMPLE_TOPIC,
                        pPublishInfo->pTopicName,
                        pPublishInfo->topicNameLength ) ) )
    {
        LogInfo( ( "Incoming Publish Topic Name: %.*s matches subscribed topic.\n"
                   "Incoming Publish message Packet Id is %u.\n"
                   "Incoming Publish Message : %.*s.\n\n",
                   pPublishInfo->topicNameLength,
                   pPublishInfo->pTopicName,
                   packetIdentifier,
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

static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo )
{
    uint16_t packetIdentifier;

    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );
    assert( pDeserializedInfo != NULL );

    packetIdentifier = pDeserializedInfo->packetIdentifier;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pDeserializedInfo->pPublishInfo != NULL );
        /* Handle incoming publish. */
        handleIncomingPublish( pDeserializedInfo->pPublishInfo, packetIdentifier );
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
                LogWarn( ( "PINGRESP should not be handled by the application "
                           "callback when using MQTT_ProcessLoop.\n\n" ) );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).\n\n",
                            pPacketInfo->type ) );
        }
    }
}

/*-----------------------------------------------------------*/

static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    bool sessionPresent;
    MQTTFixedBuffer_t networkBuffer;
    TransportInterface_t transport;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network. Network context is socket file descriptor.*/
    transport.pNetworkContext = pNetworkContext;
    transport.send = Plaintext_Send;
    transport.recv = Plaintext_Recv;

    /* Fill the values for network buffer. */
    networkBuffer.pBuffer = buffer;
    networkBuffer.size = NETWORK_BUFFER_SIZE;

    /* Initialize MQTT library. */
    mqttStatus = MQTT_Init( pMqttContext,
                            &transport,
                            Clock_GetTimeMs,
                            eventCallback,
                            &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "MQTT init failed: Status=%s.", MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
        /* Establish MQTT session by sending a CONNECT packet. */

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

        /* The maximum time interval in seconds which is allowed to elapse
         * between two Control Packets.
         * It is the responsibility of the Client to ensure that the interval between
         * Control Packets being sent does not exceed the this Keep Alive value. In the
         * absence of sending any other Control Packets, the Client MUST send a
         * PINGREQ Packet. */
        connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

        /* Username and password for authentication. Not used in this demo. */
        connectInfo.pUserName = NULL;
        connectInfo.userNameLength = 0U;
        connectInfo.pPassword = NULL;
        connectInfo.passwordLength = 0U;

        /* Send MQTT CONNECT packet to broker. */
        mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, &sessionPresent );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Connection with MQTT broker failed with status %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
        else
        {
            LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int disconnectMqttSession( MQTTContext_t * pMqttContext )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    int returnStatus = EXIT_SUCCESS;

    assert( pMqttContext != NULL );

    /* Send DISCONNECT. */
    mqttStatus = MQTT_Disconnect( pMqttContext );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Sending MQTT DISCONNECT failed with status=%s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribeToTopic( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS0. */
    pSubscriptionList[ 0 ].qos = MQTTQoS0;
    pSubscriptionList[ 0 ].pTopicFilter = MQTT_EXAMPLE_TOPIC;
    pSubscriptionList[ 0 ].topicFilterLength = MQTT_EXAMPLE_TOPIC_LENGTH;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pMqttContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 globalSubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "SUBSCRIBE sent for topic %.*s to broker.\n\n",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int unsubscribeFromTopic( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to and unsubscribes from only one topic
     * and uses QOS0. */
    pSubscriptionList[ 0 ].qos = MQTTQoS0;
    pSubscriptionList[ 0 ].pTopicFilter = MQTT_EXAMPLE_TOPIC;
    pSubscriptionList[ 0 ].topicFilterLength = MQTT_EXAMPLE_TOPIC_LENGTH;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                   globalUnsubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE sent for topic %.*s to broker.\n\n",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int publishToTopic( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTPublishInfo_t publishInfo;

    assert( pMqttContext != NULL );

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
    mqttStatus = MQTT_Publish( pMqttContext, &publishInfo, 0U );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send PUBLISH packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "PUBLISH send for topic %.*s to broker.",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribePublishLoop( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool mqttSessionEstablished = false;
    MQTTContext_t mqttContext;
    MQTTStatus_t mqttStatus;
    uint32_t publishCount = 0;
    const uint32_t maxPublishCount = MQTT_PUBLISH_COUNT_PER_LOOP;

    /* Establish MQTT session on top of TCP connection. */
    LogInfo( ( "Creating an MQTT connection to %.*s.",
               BROKER_ENDPOINT_LENGTH,
               BROKER_ENDPOINT ) );

    /* Sends an MQTT Connect packet over the already connected TCP socket
     * tcpSocket, and waits for connection acknowledgment (CONNACK) packet. */
    returnStatus = establishMqttSession( &mqttContext, pNetworkContext );

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Keep a flag for indicating if MQTT session is established. This
         * flag will mark that an MQTT DISCONNECT has to be sent at the end
         * of the demo even if there are intermediate failures. */
        mqttSessionEstablished = true;
    }

    if( returnStatus == EXIT_SUCCESS )
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
        returnStatus = subscribeToTopic( &mqttContext );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Publish messages with QOS0, receive incoming messages and
         * send keep alive messages. */
        for( publishCount = 0; publishCount < maxPublishCount; publishCount++ )
        {
            LogInfo( ( "Sending Publish to the MQTT topic %.*s.",
                       MQTT_EXAMPLE_TOPIC_LENGTH,
                       MQTT_EXAMPLE_TOPIC ) );
            returnStatus = publishToTopic( &mqttContext );

            /* Calling MQTT_ProcessLoop to process incoming publish echo, since
             * application subscribed to the same topic the broker will send
             * publish message back to the application. This function also
             * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
             * has expired since the last MQTT packet sent and receive
             * ping responses. */
            mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

            if( mqttStatus != MQTTSuccess )
            {
                LogWarn( ( "MQTT_ProcessLoop returned with status = %s.",
                           MQTT_Status_strerror( mqttStatus ) ) );
            }

            LogInfo( ( "Delay before continuing to next iteration.\n\n" ) );

            /* Leave connection idle for some time. */
            sleep( DELAY_BETWEEN_PUBLISHES_SECONDS );
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Unsubscribe from the topic. */
        LogInfo( ( "Unsubscribing from the MQTT topic %.*s.",
                   MQTT_EXAMPLE_TOPIC_LENGTH,
                   MQTT_EXAMPLE_TOPIC ) );
        returnStatus = unsubscribeFromTopic( &mqttContext );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
    }

    /* Send an MQTT Disconnect packet over the already connected TCP socket.
     * There is no corresponding response for the disconnect packet. After sending
     * disconnect, client must close the network connection. */
    if( mqttSessionEstablished == true )
    {
        LogInfo( ( "Disconnecting the MQTT connection with %.*s.",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT ) );

        if( returnStatus == EXIT_FAILURE )
        {
            /* Returned status is not used to update the local status as there
             * were failures in demo execution. */
            ( void ) disconnectMqttSession( &mqttContext );
        }
        else
        {
            returnStatus = disconnectMqttSession( &mqttContext );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TCP connection established using POSIX sockets.
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS0 and therefore does not implement any retransmission
 * mechanism for Publish messages. This example runs forever, if connection to
 * the broker goes down, the code tries to reconnect to the broker with exponential
 * backoff mechanism.
 *
 */
int main( int argc,
          char ** argv )
{
    int returnStatus = EXIT_SUCCESS;
    NetworkContext_t networkContext;

    ( void ) argc;
    ( void ) argv;

    for( ; ; )
    {
        /* Attempt to connect to the MQTT broker. If connection fails, retry after
         * a timeout. Timeout value will be exponentially increased till the maximum
         * attempts are reached or maximum timeout value is reached. The function
         * returns EXIT_FAILURE if the TCP connection cannot be established to
         * broker after configured number of attempts. */
        returnStatus = connectToServerWithBackoffRetries( &networkContext );

        if( returnStatus == EXIT_FAILURE )
        {
            /* Log error to indicate connection failure after all
             * reconnect attempts are over. */
            LogError( ( "Failed to connect to MQTT broker %.*s.",
                        BROKER_ENDPOINT_LENGTH,
                        BROKER_ENDPOINT ) );
        }
        else
        {
            /* If TCP connection is successful, execute Subscribe/Publish loop. */
            returnStatus = subscribePublishLoop( &networkContext );
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Log message indicating an iteration completed successfully. */
            LogInfo( ( "Demo completed successfully." ) );
        }

        /* Close the TCP connection.  */
        ( void ) Plaintext_Disconnect( &networkContext );

        LogInfo( ( "Short delay before starting the next iteration....\n" ) );
        sleep( MQTT_SUBPUB_LOOP_DELAY_SECONDS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/
