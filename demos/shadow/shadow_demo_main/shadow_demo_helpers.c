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
 * @file shadow_demo_helpers.c
 *
 * @brief This file provides helper functions used by shadow demo application to
 * do MQTT operation based on mutually authenticated TLS connection.
 *
 * A mutually authenticated TLS connection is used to connect to the AWS IoT
 * MQTT message broker in this example. Define ROOT_CA_CERT_PATH,
 * CLIENT_CERT_PATH, and CLIENT_PRIVATE_KEY_PATH in demo_config.h to achieve
 * mutual authentication.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Shadow includes */
#include "shadow_demo_helpers.h"

/* POSIX includes. */
#include <unistd.h>

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/* Clock for timer. */
#include "clock.h"

/* AWS IoT Core TLS ALPN definitions for MQTT authentication */
#include "aws_iot_alpn_defs.h"

/**
 * These configuration settings are required to run the shadow demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef AWS_IOT_ENDPOINT
    #error "Please define AWS IoT MQTT broker endpoint(AWS_IOT_ENDPOINT) in demo_config.h."
#endif
#ifndef ROOT_CA_CERT_PATH
    #error "Please define path to Root CA certificate of the MQTT broker(ROOT_CA_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_CERT_PATH
    #error "Please define path to client certificate(CLIENT_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_PRIVATE_KEY_PATH
    #error "Please define path to client private key(CLIENT_PRIVATE_KEY_PATH) in demo_config.h."
#endif
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * Provide default values for undefined configuration settings.
 */
#ifndef AWS_MQTT_PORT
    #define AWS_MQTT_PORT    ( 8883 )
#endif

#ifndef NETWORK_BUFFER_SIZE
    #define NETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of MQTT server host name.
 */
#define AWS_IOT_ENDPOINT_LENGTH                  ( ( uint16_t ) ( sizeof( AWS_IOT_ENDPOINT ) - 1 ) )

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH                 ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

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
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS                  ( 1000U )


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
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 1000U )

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
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 1000 )

/**
 * @brief The MQTT metrics string expected by AWS IoT.
 */
#define METRICS_STRING                      "?SDK=" OS_NAME "&Version=" OS_VERSION "&Platform=" HARDWARE_PLATFORM_NAME "&MQTTLib=" MQTT_LIB

/**
 * @brief The length of the MQTT metrics string expected by AWS IoT.
 */
#define METRICS_STRING_LENGTH               ( ( uint16_t ) ( sizeof( METRICS_STRING ) - 1 ) )

/**
 * @brief The length of the outgoing publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for outgoing publishes.
 */
#define OUTGOING_PUBLISH_RECORD_LEN         ( 10U )

/**
 * @brief The length of the incoming publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for incoming publishes.
 */
#define INCOMING_PUBLISH_RECORD_LEN         ( 10U )

/*-----------------------------------------------------------*/

/**
 * @brief Structure to keep the MQTT publish packets until an ack is received
 * for QoS1 publishes.
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

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Packet Identifier updated when an ACK packet is received.
 *
 * It is used to match an expected ACK for a transmitted packet.
 */
static uint16_t globalAckPacketIdentifier = 0U;

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

/**
 * @brief The MQTT context used for MQTT operation.
 */
static MQTTContext_t mqttContext = { 0 };

/**
 * @brief The network context used for Openssl operation.
 */
static NetworkContext_t networkContext = { 0 };

/**
 * @brief The parameters for Openssl operation.
 */
static OpensslParams_t opensslParams = { 0 };

/**
 * @brief The flag to indicate the mqtt session changed.
 */
static bool mqttSessionEstablished = false;

/**
 * @brief Array to track the outgoing publish records for outgoing publishes
 * with QoS > 0.
 *
 * This is passed into #MQTT_InitStatefulQoS to allow for QoS > 0.
 *
 */
static MQTTPubAckInfo_t pOutgoingPublishRecords[ OUTGOING_PUBLISH_RECORD_LEN ];

/**
 * @brief Array to track the incoming publish records for incoming publishes
 * with QoS > 0.
 *
 * This is passed into #MQTT_InitStatefulQoS to allow for QoS > 0.
 *
 */
static MQTTPubAckInfo_t pIncomingPublishRecords[ INCOMING_PUBLISH_RECORD_LEN ];

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
 * Timeout value will exponentially increase until maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext );

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
 * the broker. This function handles the resending of the QoS1 publish packets,
 * which are maintained locally.
 *
 * @param[in] pMqttContext MQTT context pointer.
 */
static int handlePublishResend( MQTTContext_t * pMqttContext );

/**
 * @brief Wait for an expected ACK packet to be received.
 *
 * This function handles waiting for an expected ACK packet by calling
 * #MQTT_ProcessLoop and waiting for #mqttCallback to set the global ACK
 * packet identifier to the expected ACK packet identifier.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] usPacketIdentifier Packet identifier for expected ACK packet.
 * @param[in] ulTimeout Maximum duration to wait for expected ACK packet.
 *
 * @return EXIT_SUCCESS if the expected ACK packet was received, EXIT_FAILURE
 * otherwise.
 */
static int waitForPacketAck( MQTTContext_t * pMqttContext,
                             uint16_t usPacketIdentifier,
                             uint32_t ulTimeout );

/**
 * @brief Call #MQTT_ProcessLoop in a loop for the duration of a timeout or
 * #MQTT_ProcessLoop returns a failure.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] ulTimeoutMs Duration to call #MQTT_ProcessLoop for.
 *
 * @return Returns the return value of the last call to #MQTT_ProcessLoop.
 */
static MQTTStatus_t processLoopWithTimeout( MQTTContext_t * pMqttContext,
                                            uint32_t ulTimeoutMs );

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    BackoffAlgorithmContext_t reconnectParams;
    ServerInfo_t serverInfo;
    OpensslCredentials_t opensslCredentials;
    uint16_t nextRetryBackOff = 0U;
    struct timespec tp;

    /* Set the pParams member of the network context with desired transport. */
    pNetworkContext->pParams = &opensslParams;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = AWS_IOT_ENDPOINT;
    serverInfo.hostNameLength = AWS_IOT_ENDPOINT_LENGTH;
    serverInfo.port = AWS_MQTT_PORT;

    /* Initialize credentials for establishing TLS session. */
    ( void ) memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
    opensslCredentials.pPrivateKeyPath = CLIENT_PRIVATE_KEY_PATH;
    opensslCredentials.sniHostName = AWS_IOT_ENDPOINT;

    if( AWS_MQTT_PORT == 443 )
    {
        /* Pass the ALPN protocol name depending on the port being used.
         * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
         * in the link below.
         * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
         */
        opensslCredentials.pAlpnProtos = AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL;
        opensslCredentials.alpnProtosLen = AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL_LEN;
    }

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
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TLS session with the MQTT broker. This example connects
         * to the MQTT broker as specified in AWS_IOT_ENDPOINT and AWS_MQTT_PORT
         * at the demo config header. */
        LogInfo( ( "Establishing a TLS session to %.*s:%d.",
                   AWS_IOT_ENDPOINT_LENGTH,
                   AWS_IOT_ENDPOINT,
                   AWS_MQTT_PORT ) );
        opensslStatus = Openssl_Connect( pNetworkContext,
                                         &serverInfo,
                                         &opensslCredentials,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( opensslStatus != OPENSSL_SUCCESS )
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
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    return returnStatus;
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
            LogInfo( ( "Cleaned up outgoing publish packet with packet id %u.",
                       packetId ) );
            break;
        }
    }
}

/*-----------------------------------------------------------*/

static int waitForPacketAck( MQTTContext_t * pMqttContext,
                             uint16_t usPacketIdentifier,
                             uint32_t ulTimeout )
{
    uint32_t ulMqttProcessLoopEntryTime;
    uint32_t ulMqttProcessLoopTimeoutTime;
    uint32_t ulCurrentTime;

    MQTTStatus_t eMqttStatus = MQTTSuccess;
    int returnStatus = EXIT_FAILURE;

    /* Reset the ACK packet identifier being received. */
    globalAckPacketIdentifier = 0U;

    ulCurrentTime = pMqttContext->getTime();
    ulMqttProcessLoopEntryTime = ulCurrentTime;
    ulMqttProcessLoopTimeoutTime = ulCurrentTime + ulTimeout;

    /* Call MQTT_ProcessLoop multiple times until the expected packet ACK
     * is received, a timeout happens, or MQTT_ProcessLoop fails. */
    while( ( globalAckPacketIdentifier != usPacketIdentifier ) &&
           ( ulCurrentTime < ulMqttProcessLoopTimeoutTime ) &&
           ( eMqttStatus == MQTTSuccess || eMqttStatus == MQTTNeedMoreBytes ) )
    {
        /* Event callback will set #globalAckPacketIdentifier when receiving
         * appropriate packet. */
        eMqttStatus = MQTT_ProcessLoop( pMqttContext );
        ulCurrentTime = pMqttContext->getTime();
    }

    if( ( ( eMqttStatus != MQTTSuccess ) && ( eMqttStatus != MQTTNeedMoreBytes ) ) ||
        ( globalAckPacketIdentifier != usPacketIdentifier ) )
    {
        LogError( ( "MQTT_ProcessLoop failed to receive ACK packet: Expected ACK Packet ID=%02X, LoopDuration=%u, Status=%s",
                    usPacketIdentifier,
                    ( ulCurrentTime - ulMqttProcessLoopEntryTime ),
                    MQTT_Status_strerror( eMqttStatus ) ) );
    }
    else
    {
        returnStatus = EXIT_SUCCESS;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t processLoopWithTimeout( MQTTContext_t * pMqttContext,
                                            uint32_t ulTimeoutMs )
{
    uint32_t ulMqttProcessLoopTimeoutTime;
    uint32_t ulCurrentTime;

    MQTTStatus_t eMqttStatus = MQTTSuccess;

    ulCurrentTime = pMqttContext->getTime();
    ulMqttProcessLoopTimeoutTime = ulCurrentTime + ulTimeoutMs;

    /* Call MQTT_ProcessLoop multiple times a timeout happens, or
     * MQTT_ProcessLoop fails. */
    while( ( ulCurrentTime < ulMqttProcessLoopTimeoutTime ) &&
           ( eMqttStatus == MQTTSuccess || eMqttStatus == MQTTNeedMoreBytes ) )
    {
        eMqttStatus = MQTT_ProcessLoop( pMqttContext );
        ulCurrentTime = pMqttContext->getTime();
    }

    return eMqttStatus;
}

/*-----------------------------------------------------------*/

void HandleOtherIncomingPacket( MQTTPacketInfo_t * pPacketInfo,
                                uint16_t packetIdentifier )
{
    /* Handle other packets. */
    switch( pPacketInfo->type )
    {
        case MQTT_PACKET_TYPE_SUBACK:
            LogInfo( ( "MQTT_PACKET_TYPE_SUBACK." ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            assert( globalSubscribePacketIdentifier == packetIdentifier );
            /* Update the global ACK packet identifier. */
            globalAckPacketIdentifier = packetIdentifier;
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            LogInfo( ( "MQTT_PACKET_TYPE_UNSUBACK." ) );
            /* Make sure ACK packet identifier matches with Request packet identifier. */
            assert( globalUnsubscribePacketIdentifier == packetIdentifier );
            /* Update the global ACK packet identifier. */
            globalAckPacketIdentifier = packetIdentifier;
            break;

        case MQTT_PACKET_TYPE_PINGRESP:

            /* Nothing to be done from application as library handles
             * PINGRESP. */
            LogWarn( ( "PINGRESP should not be handled by the application "
                       "callback when using MQTT_ProcessLoop." ) );
            break;

        case MQTT_PACKET_TYPE_PUBACK:
            LogInfo( ( "PUBACK received for packet id %u.",
                       packetIdentifier ) );
            /* Cleanup publish packet when a PUBACK is received. */
            cleanupOutgoingPublishWithPacketID( packetIdentifier );
            /* Update the global ACK packet identifier. */
            globalAckPacketIdentifier = packetIdentifier;
            break;

        /* Any other packet type is invalid. */
        default:
            LogError( ( "Unknown packet type received:(%02x).",
                        pPacketInfo->type ) );
    }
}

/*-----------------------------------------------------------*/

static int handlePublishResend( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t index = 0U;

    assert( outgoingPublishPackets != NULL );

    /* Resend all the QoS1 publishes still in the array. These are the
     * publishes that hasn't received a PUBACK. When a PUBACK is
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
                LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.",
                           outgoingPublishPackets[ index ].packetId ) );
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int EstablishMqttSession( MQTTEventCallback_t eventCallback )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
    MQTTFixedBuffer_t networkBuffer;
    TransportInterface_t transport = { NULL };
    bool createCleanSession = false;
    MQTTContext_t * pMqttContext = &mqttContext;
    NetworkContext_t * pNetworkContext = &networkContext;
    bool sessionPresent = false;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Initialize the mqtt context and network context. */
    ( void ) memset( pMqttContext, 0U, sizeof( MQTTContext_t ) );
    ( void ) memset( pNetworkContext, 0U, sizeof( NetworkContext_t ) );

    returnStatus = connectToServerWithBackoffRetries( pNetworkContext );

    if( returnStatus != EXIT_SUCCESS )
    {
        /* Log error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to MQTT broker %.*s.",
                    AWS_IOT_ENDPOINT_LENGTH,
                    AWS_IOT_ENDPOINT ) );
    }
    else
    {
        /* Fill in TransportInterface send and receive function pointers.
         * For this demo, TCP sockets are used to send and receive data
         * from network. Network context is SSL context for OpenSSL.*/
        transport.pNetworkContext = pNetworkContext;
        transport.send = Openssl_Send;
        transport.recv = Openssl_Recv;

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
            LogError( ( "MQTT_Init failed: Status = %s.", MQTT_Status_strerror( mqttStatus ) ) );
        }
        else
        {
            mqttStatus = MQTT_InitStatefulQoS( pMqttContext,
                                               pOutgoingPublishRecords,
                                               OUTGOING_PUBLISH_RECORD_LEN,
                                               pIncomingPublishRecords,
                                               INCOMING_PUBLISH_RECORD_LEN );

            if( mqttStatus != MQTTSuccess )
            {
                returnStatus = EXIT_FAILURE;
                LogError( ( "MQTT_InitStatefulQoS failed: Status = %s.", MQTT_Status_strerror( mqttStatus ) ) );
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
                connectInfo.pUserName = METRICS_STRING;
                connectInfo.userNameLength = METRICS_STRING_LENGTH;
                connectInfo.pPassword = NULL;
                connectInfo.passwordLength = 0U;

                /* Send MQTT CONNECT packet to broker. */
                mqttStatus = MQTT_Connect( pMqttContext,
                                           &connectInfo,
                                           NULL,
                                           CONNACK_RECV_TIMEOUT_MS,
                                           &sessionPresent );

                if( mqttStatus != MQTTSuccess )
                {
                    returnStatus = EXIT_FAILURE;
                    LogError( ( "Connection with MQTT broker failed with status %u.", mqttStatus ) );
                }
                else
                {
                    LogInfo( ( "MQTT connection successfully established with broker." ) );
                }
            }

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
                               " Cleaning up all the stored outgoing publishes." ) );

                    /* Clean up the outgoing publishes waiting for ack as this new
                     * connection doesn't re-establish an existing session. */
                    cleanupOutgoingPublishes();
                }
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t DisconnectMqttSession( void )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    int returnStatus = EXIT_SUCCESS;
    MQTTContext_t * pMqttContext = &mqttContext;
    NetworkContext_t * pNetworkContext = &networkContext;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    if( mqttSessionEstablished == true )
    {
        /* Send DISCONNECT. */
        mqttStatus = MQTT_Disconnect( pMqttContext );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Sending MQTT DISCONNECT failed with status=%u.",
                        mqttStatus ) );
            returnStatus = EXIT_FAILURE;
        }
    }

    /* End TLS session, then close TCP connection. */
    ( void ) Openssl_Disconnect( pNetworkContext );

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t SubscribeToTopic( const char * pTopicFilter,
                          uint16_t topicFilterLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

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
        LogInfo( ( "SUBSCRIBE topic %.*s to broker.",
                   topicFilterLength,
                   pTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        returnStatus = waitForPacketAck( pMqttContext,
                                         globalSubscribePacketIdentifier,
                                         MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t UnsubscribeFromTopic( const char * pTopicFilter,
                              uint16_t topicFilterLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

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
        LogInfo( ( "UNSUBSCRIBE sent topic %.*s to broker.",
                   topicFilterLength,
                   pTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        returnStatus = waitForPacketAck( pMqttContext,
                                         globalUnsubscribePacketIdentifier,
                                         MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t PublishToTopic( const char * pTopicFilter,
                        int32_t topicFilterLength,
                        const char * pPayload,
                        size_t payloadLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t publishIndex = MAX_OUTGOING_PUBLISHES;
    MQTTContext_t * pMqttContext = &mqttContext;

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    returnStatus = getNextFreeIndexForOutgoingPublishes( &publishIndex );

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message." ) );
    }
    else
    {
        LogInfo( ( "Published payload: %s", pPayload ) );
        /* This example publishes to only one topic and uses QOS1. */
        outgoingPublishPackets[ publishIndex ].pubInfo.qos = MQTTQoS1;
        outgoingPublishPackets[ publishIndex ].pubInfo.pTopicName = pTopicFilter;
        outgoingPublishPackets[ publishIndex ].pubInfo.topicNameLength = topicFilterLength;
        outgoingPublishPackets[ publishIndex ].pubInfo.pPayload = pPayload;
        outgoingPublishPackets[ publishIndex ].pubInfo.payloadLength = payloadLength;

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
            LogInfo( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.",
                       topicFilterLength,
                       pTopicFilter,
                       outgoingPublishPackets[ publishIndex ].packetId ) );

            /* Calling MQTT_ProcessLoop to process incoming publish echo, since
             * application subscribed to the same topic the broker will send
             * publish message back to the application. This function also
             * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
             * has expired since the last MQTT packet sent and receive
             * ping responses. */
            mqttStatus = processLoopWithTimeout( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

            if( ( mqttStatus != MQTTSuccess ) && ( mqttStatus != MQTTNeedMoreBytes ) )
            {
                LogWarn( ( "MQTT_ProcessLoop returned with status = %u.",
                           mqttStatus ) );
            }
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/
