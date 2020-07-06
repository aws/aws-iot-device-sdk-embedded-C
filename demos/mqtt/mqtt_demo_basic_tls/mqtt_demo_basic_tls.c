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

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* MQTT API header. */
#include "mqtt.h"

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/* Reconnect parameters. */
#include "reconnect.h"

/**
 * These configuration settings are required to run the mutual auth demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef ROOT_CA_CERT_PATH
    #error "Please define path to root ca certificate of the AWS IoT MQTT broker(ROOT_CA_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * Provide default values for undefined configuration settings.
 */
#ifndef BROKER_PORT
    #define BROKER_PORT    ( 8883 )
#endif

#ifndef NETWORK_BUFFER_SIZE
    #define NETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH            ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

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
 * @brief Delay in seconds between two iterations of subscribePublishLoop()
 */
#define MQTT_SUBPUB_LOOP_DELAY_SECONDS      ( 5U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 200 )

/*-----------------------------------------------------------*/

/**
 * @brief Structure to keep the MQTT publish packets until an ack is received
 * for QoS2 publishes.
 */
typedef struct PublishPackets
{
    /**
     * @brief Packet identifier of the publish packet.
     */
    uint16_t packetId;

    /**
     * @brief Publish info of the publish packet.
     */
    MQTTPublishInfo_t pubInfo;
} PublishPackets_t;

/*-----------------------------------------------------------*/

/**
 * @brief globalEntryTime Entry time into the application to use as a reference
 * timestamp in #getTimeMs function. #getTimeMs will always return the difference
 * of current time with the globalEntryTime. This will reduce the chances of
 * overflow for 32 bit unsigned integer used for holding the timestamp.
 */
static uint32_t globalEntryTimeMs = 0U;

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
 * @brief Array to keep the outgoing publish messages.
 * These stored outgoing publish messages are kept until a successful ack
 * is received.
 */
static PublishPackets_t outgoingPublishPackets[ MAX_OUTGOING_PUBLISHES ] = { 0 };

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/*-----------------------------------------------------------*/

/**
 * @brief connect to MQTT broker with reconnection retries.
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increased till maximum
 * timeout value is reached or the number of attemps are exhausted.
 *
 * @param[out] pNetworkContext Network context pointer containing TCP socket
 * file descriptor referring to the established connection.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext );

/**
 * @brief A function that connects to MQTT broker,
 * subscribes a topic, Publishes to the same
 * topic MQTT_PUBLISH_COUNT_PER_LOOP number of times, and verifies if it
 * receives the Publish message back.
 *
 * @param[in] pNetworkContext Network context pointer containing TCP socket.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int subscribePublishLoop( NetworkContext_t * pNetworkContext );

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
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] packetIdentifier Packet identifier of the incoming packet.
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pNetworkContext Network context pointer for OpenSSL.
 * @param[in] createCleanSession Creates a new MQTT session if true.
 * If false, tries to establish the existing session if there was session
 * already present in broker.
 * @param[out] pSessionPresent Session was already present in the broker or not.
 * Session present response is obtained from the CONNACK from broker.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent );

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
static MQTTStatus_t unsubscribeFromTopic( MQTTContext_t * pMqttContext );

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

/**
 * @brief Function to get the free index at which an outgoing publish
 * can be stored.
 *
 * @param[out] pIndex The output parameter to return the index at which an
 * outgoing publish message can be stored.
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
static void cleanupOutgoingPublishes( void );

/**
 * @brief Function to clean up the publish packet with the given packet id.
 *
 * @param[in] packetId Packet identifier of the packet to be cleaned up from
 * the array.
 */
static void cleanupOutgoingPublishWithPacketID( uint16_t packetId );

/**
 * @brief Function to resend the publishes if a session is re-established with
 * the broker. This function handles the resending of the QoS2 publish packets,
 * which are maintained locally.
 *
 * @param[in] pMqttContext MQTT context pointer.
 */
static int handlePublishResend( MQTTContext_t * pMqttContext );

/*-----------------------------------------------------------*/

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool backoffSuccess = true;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    TransportReconnectParams_t reconnectParams;
    ServerInfo_t serverInfo;
    OpensslCredentials_t opensslCredentials;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = BROKER_ENDPOINT;
    serverInfo.hostNameLength = BROKER_ENDPOINT_LENGTH;
    serverInfo.port = BROKER_PORT;

    /* Initialize credentials for establishing TLS session. */
    memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;

    /* Initialize reconnect attempts and interval */
    Transport_ReconnectParamsReset( &reconnectParams );

    /* Attempt to connect to MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase till maximum
     * attemps are reached.
     */
    do
    {
        /* Establish a TCP connection with the MQTT broker. This example connects
         * to the MQTT broker as specified in AWS_IOT_ENDPOINT and AWS_MQTT_PORT at
         * the top of this file. */
        LogInfo( ( "Creating a TCP connection to %.*s:%d.",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT,
                   BROKER_PORT ) );
        opensslStatus = Openssl_Connect( pNetworkContext,
                                         &serverInfo,
                                         &opensslCredentials,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( opensslStatus != OPENSSL_SUCCESS )
        {
            LogWarn( ( "Connection to the broker failed, sleeping %d seconds before the next attempt.",
                       ( reconnectParams.reconnectTimeoutSec > MAX_RECONNECT_TIMEOUT_SECONDS ) ? MAX_RECONNECT_TIMEOUT_SECONDS : reconnectParams.reconnectTimeoutSec ) );
            backoffSuccess = Transport_ReconnectBackoffAndSleep( &reconnectParams );
        }

        if( backoffSuccess == false )
        {
            LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            returnStatus = EXIT_FAILURE;
        }
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( backoffSuccess == true ) );

    return returnStatus;
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
    int returnStatus = EXIT_FAILURE;
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( pIndex != NULL );

    for( index = 0; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        /* A free index is marked by invalid packet id.
         * Check if the the index has a free slot. */
        if( outgoingPublishPackets[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            returnStatus = EXIT_SUCCESS;
            break;
        }
    }

    /* Copy the available index into the output param. */
    *pIndex = index;

    return returnStatus;
}
/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishAt( uint8_t index )
{
    assert( outgoingPublishPackets != NULL );
    assert( index < MAX_OUTGOING_PUBLISHES );

    /* Clear the outgoing publish packet. */
    ( void ) memset( &( outgoingPublishPackets[ index ] ),
                     0x00,
                     sizeof( outgoingPublishPackets[ index ] ) );
}

/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishes( void )
{
    assert( outgoingPublishPackets != NULL );

    /* Clean up all the outgoing publish packets. */
    ( void ) memset( outgoingPublishPackets, 0x00, sizeof( outgoingPublishPackets ) );
}

/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishWithPacketID( uint16_t packetId )
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

static int handlePublishResend( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t index = 0U;

    assert( outgoingPublishPackets != NULL );

    /* Resend all the QoS2 publishes still in the array. These are the
     * publishes that hasn't received a PUBREC. When a PUBREC is
     * received, the publish is removed from the array. */
    for( index = 0U; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId != MQTT_PACKET_ID_INVALID )
        {
            outgoingPublishPackets[ index ].pubInfo.dup = true;

            LogInfo( ( "Sending duplicate PUBLISH with packet id %u.",
                       outgoingPublishPackets[ index ].packetId ) );
            mqttStatus = MQTT_Publish( pMqttContext,
                                       &outgoingPublishPackets[ index ].pubInfo,
                                       outgoingPublishPackets[ index ].packetId );

            if( mqttStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %u.",
                            outgoingPublishPackets[ index ].packetId,
                            mqttStatus ) );
                returnStatus = EXIT_FAILURE;
                break;
            }
            else
            {
                LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.\n\n",
                           outgoingPublishPackets[ index ].packetId ) );
            }
        }
    }

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
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo )
{
    assert( pMqttContext != NULL );
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
                LogInfo( ( "PINGRESP received.\n\n" ) );
                break;

            case MQTT_PACKET_TYPE_PUBREC:
                LogInfo( ( "PUBREC received for packet id %u.",
                           packetIdentifier ) );
                /* Cleanup publish packet when a PUBREC is received. */
                cleanupOutgoingPublishWithPacketID( packetIdentifier );
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

static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    TransportInterface_t transport;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network. Network context is SSL context for OpenSSL.*/
    transport.pNetworkContext = pNetworkContext;
    transport.send = Openssl_Send;
    transport.recv = Openssl_Recv;

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
    mqttStatus = MQTT_Init( pMqttContext, &transport, &callbacks, &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "MQTT init failed with status %u.", mqttStatus ) );
    }
    else
    {
        /* Establish MQTT session by sending a CONNECT packet. */

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
        mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, pSessionPresent );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Connection with MQTT broker failed with status %u.", mqttStatus ) );
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
        LogError( ( "Sending MQTT DISCONNECT failed with status=%u.",
                    mqttStatus ) );
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

    /* This example subscribes to only one topic and uses QOS2. */
    pSubscriptionList[ 0 ].qos = MQTTQoS2;
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
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
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

static MQTTStatus_t unsubscribeFromTopic( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to and unsubscribes from only one topic
     * and uses QOS2. */
    pSubscriptionList[ 0 ].qos = MQTTQoS2;
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
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
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
    uint8_t publishIndex = MAX_OUTGOING_PUBLISHES;

    assert( pMqttContext != NULL );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    returnStatus = getNextFreeIndexForOutgoingPublishes( &publishIndex );

    if( returnStatus == EXIT_FAILURE )
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
        outgoingPublishPackets[ publishIndex ].packetId = MQTT_GetPacketId( pMqttContext );

        /* Send PUBLISH packet. */
        mqttStatus = MQTT_Publish( pMqttContext,
                                   &outgoingPublishPackets[ publishIndex ].pubInfo,
                                   outgoingPublishPackets[ publishIndex ].packetId );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.",
                        mqttStatus ) );
            cleanupOutgoingPublishAt( publishIndex );
            returnStatus = EXIT_FAILURE;
        }
        else
        {
            LogInfo( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.\n\n",
                       MQTT_EXAMPLE_TOPIC_LENGTH,
                       MQTT_EXAMPLE_TOPIC,
                       outgoingPublishPackets[ publishIndex ].packetId ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribePublishLoop( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool mqttSessionEstablished = false, sessionPresent;
    MQTTContext_t mqttContext;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint32_t publishCount = 0;
    const uint32_t maxPublishCount = MQTT_PUBLISH_COUNT_PER_LOOP;

    /* Get the entry time to application. */
    globalEntryTimeMs = getTimeMs();

    /* Establish MQTT session on top of TCP+TLS connection. */
    LogInfo( ( "Creating an MQTT connection to %.*s.",
               BROKER_ENDPOINT_LENGTH,
               BROKER_ENDPOINT ) );

    /* Sends an MQTT Connect packet using the established TLS session,
     * then waits for connection acknowledgment (CONNACK) packet. */
    returnStatus = establishMqttSession( &mqttContext, pNetworkContext, false, &sessionPresent );

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Keep a flag for indicating if MQTT session is established. This
         * flag will mark that an MQTT DISCONNECT has to be sent at the end
         * of the demo even if there are intermediate failures. */
        mqttSessionEstablished = true;
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Check if session is present and if there are any outgoing publishes
         * that need to resend. This is only valid if the broker is
         * re-establishing a session which was already present. */
        if( sessionPresent == true )
        {
            LogInfo( ( "An MQTT session with broker is re-established. "
                       "Resending unacked publishes." ) );

            /* Handle all the resend of publish messages. */
            returnStatus = handlePublishResend( &mqttContext );
        }
        else
        {
            LogInfo( ( "A clean MQTT connection is established."
                       " Cleaning up all the stored outgoing publishes.\n\n" ) );

            /* Clean up the outgoing publishes waiting for ack as this new
             * connection doesn't re-establish an existing session. */
            cleanupOutgoingPublishes();
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in MQTT_EXAMPLE_TOPIC at the top of this file by sending a
         * subscribe packet. This client will then publish to the same topic it
         * subscribed to, so it will expect all the messages it sends to the broker
         * to be sent back to it from the broker. This demo uses QOS2 in Subscribe,
         * therefore, the Publish messages received from the broker will have QOS2. */
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
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Publish messages with QOS2, receive incoming messages and
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
                LogWarn( ( "MQTT_ProcessLoop returned with status = %u.",
                           mqttStatus ) );
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
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
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
 * over the TLS connection established using OpenSSL.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS2 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBREC
 * are resent in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBREC is received.
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
         * attemps are reached or maximum timout value is reached. The function
         * returns EXIT_FAILURE if the TCP connection cannot be established to
         * broker after configured number of attemps. */
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
            /* If TLS session is established, execute Subscribe/Publish loop. */
            returnStatus = subscribePublishLoop( &networkContext );
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Log message indicating an iteration completed successfully. */
            LogInfo( ( "Demo completed successfully." ) );
        }

        /* End TLS session, then close TCP connection. */
        ( void ) Openssl_Disconnect( &networkContext );

        LogInfo( ( "Short delay before starting the next iteration....\n" ) );
        sleep( MQTT_SUBPUB_LOOP_DELAY_SECONDS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/
