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
 * A mutually authenticated TLS connection is used to connect to the AWS IoT
 * MQTT message broker in this example. Define ROOT_CA_CERT_PATH,
 * CLIENT_CERT_PATH, and CLIENT_PRIVATE_KEY_PATH in demo_config.h to achieve
 * mutual authentication.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS1 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBACK
 * are resent in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBACK is received.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <netdb.h>
#include <poll.h>
#include <time.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

/* Demo Config header. */
#include "demo_config.h"

/* MQTT API header. */
#include "mqtt.h"

/**
 * These configuration settings are required to run the mutual auth demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef AWS_IOT_ENDPOINT
    #error "Please define AWS IoT MQTT broker endpoint(AWS_IOT_ENDPOINT) in demo_config.h."
#endif
#ifndef ROOT_CA_CERT_PATH
    #error "Please define path to root ca certificate of the AWS IoT MQTT broker(ROOT_CA_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_CERT_PATH
    #error "Please define path to client certificate(CLIENT_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_PRIVATE_KEY_PATH
    #error "Please define path to client private key(CLIENT_PRIVATE_KEY_PATH) in demo_config.h."
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

#ifndef CLIENT_IDENTIFIER
    #define CLIENT_IDENTIFIER    "testclient"
#endif

/**
 * @brief Length of MQTT server host name.
 */
#define AWS_IOT_ENDPOINT_LENGTH             ( ( uint16_t ) ( sizeof( AWS_IOT_ENDPOINT ) - 1 ) )

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH            ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief ALPN protocol name for AWS IoT MQTT.
 *
 * This will be used if the AWS_MQTT_PORT is configured as 443 for AWS IoT MQTT broker.
 * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
 * in the link below.
 * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
 */
#define ALPN_PROTOCOL_NAME                  "\x0ex-amzn-mqtt-ca"

/**
 * @brief Length of ALPN protocol name.
 */
#define ALPN_PROTOCOL_NAME_LENGTH           ( ( uint16_t ) ( sizeof( ALPN_PROTOCOL_NAME ) - 1 ) )

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
 * @brief Timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 20 )

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

/*-----------------------------------------------------------*/

/**
 * @brief Creates a TCP connection to the MQTT broker as specified by
 * AWS_IOT_ENDPOINT and AWS_MQTT_PORT defined in the demo_config.h file.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 * @param[out] pTcpSocket The output parameter to return the created socket
 * descriptor.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pTcpSocket );

/**
 * @brief Reads credentials from the filesystem.
 *
 * Uses OpenSSL to import the root CA certificate, client certificate, and
 * client certificate private key.
 *
 * @param[in] pSslContext Destination for the imported credentials.
 * @param[in] pRootCaPath Path to the root CA certificate.
 * @param[in] pClientCertPath Path to the client certificate.
 * @param[in] pCertPrivateKeyPath Path to the client private key.
 *
 * @return 1 if all credentials were successfully read; 0 otherwise.
 */
static int readCredentials( SSL_CTX * pSslContext,
                            const char * pRootCaPath,
                            const char * pClientCertPath,
                            const char * pCertPrivateKeyPath );

/**
 * @brief Set up a TLS connection over an existing TCP connection.
 *
 * @param[in] tcpSocket Socket descriptor corresponding to the existing TCP connection.
 * @param[in] pAlpnProtos List of ALPN protocols available to be negotiated.
 * @param[in] alpnProtosLen Length of the ALPN protocols list.
 * @param[out] pSslContext The output parameter to return the created SSL context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int tlsSetup( int tcpSocket,
                     const char * pAlpnProtos,
                     size_t alpnProtosLen,
                     SSL ** pSslContext );


/**
 * @brief The transport send function provided to the MQTT context.
 *
 * @param[in] pNetworkContext Pointer to SSL context.
 * @param[in] pMessage Data to send.
 * @param[in] bytesToSend Length of data to send.
 *
 * @return Number of bytes sent; negative value on error;
 * 0 for timeout or 0 bytes sent.
 */
static int32_t transportSend( NetworkContext_t pNetworkContext,
                              const void * pMessage,
                              size_t bytesToSend );

/**
 * @brief The transport receive function provided to the MQTT context.
 *
 * @param[in] pNetworkContext Pointer to SSL context.
 * @param[out] pBuffer Buffer for receiving data.
 * @param[in] bytesToRecv Length of data to be received.
 *
 * @return Number of bytes received; negative value on error;
 * 0 for timeout.
 */
static int32_t transportRecv( NetworkContext_t pNetworkContext,
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
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
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
static void cleanupOutgoingPublishes();

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

static int readCredentials( SSL_CTX * pSslContext,
                            const char * pRootCaPath,
                            const char * pClientCertPath,
                            const char * pCertPrivateKeyPath )
{
    int sslStatus = 0, fcloseStatus = 0;
    X509 * pRootCa = NULL;
    FILE * pRootCaFile = NULL;

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. Start with the
     * root certificate. */
    if( ( pRootCaPath != NULL ) &&
        ( strlen( pRootCaPath ) != 0 ) )
    {
        LogDebug( ( "Opening root certificate %s.", pRootCaPath ) );
        pRootCaFile = fopen( pRootCaPath, "r" );

        if( pRootCaFile == NULL )
        {
            LogError( ( "Failed to open %s.", pRootCaPath ) );
        }
        else
        {
            /* Read the root CA into an X509 object, then close its file handle. */
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

            if( pRootCa == NULL )
            {
                LogError( ( "Failed to parse root CA." ) );
            }
            else
            {
                sslStatus = 1;
                LogDebug( ( "Successfully parsed root CA." ) );
            }

            /* Close the pRootCaFile regardless of whether we succeeded to
             * parse the certificate or not. */
            fcloseStatus = fclose( pRootCaFile );

            if( fcloseStatus != 0 )
            {
                LogWarn( ( "Failed to close file %s", pRootCaPath ) );
            }
        }

        if( sslStatus == 1 )
        {
            /* Add the root CA to certificate store. */
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslContext ),
                                             pRootCa );

            if( sslStatus != 1 )
            {
                LogError( ( "Failed to add root CA to certificate store." ) );
            }
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pClientCertPath != NULL ) &&
        ( strlen( pClientCertPath ) != 0 ) )
    {
        /* Import the client certificate. */
        sslStatus = SSL_CTX_use_certificate_chain_file( pSslContext,
                                                        pClientCertPath );

        if( sslStatus != 1 )
        {
            LogError( ( "Failed to import client certificate at %s.",
                        pClientCertPath ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pCertPrivateKeyPath != NULL ) &&
        ( strlen( pCertPrivateKeyPath ) != 0 ) )
    {
        /* Import the client certificate private key. */
        sslStatus = SSL_CTX_use_PrivateKey_file( pSslContext,
                                                 pCertPrivateKeyPath,
                                                 SSL_FILETYPE_PEM );

        if( sslStatus != 1 )
        {
            LogError( ( "Failed to import client certificate private key at %s.",
                        pCertPrivateKeyPath ) );
        }
    }

    /* Free the root CA object. */
    if( pRootCa != NULL )
    {
        X509_free( pRootCa );
    }

    if( sslStatus == 1 )
    {
        LogInfo( ( "Successfully imported server root CA, client certificate and "
                   "client private key." ) );
    }

    return sslStatus;
}

/*-----------------------------------------------------------*/

static int tlsSetup( int tcpSocket,
                     const char * pAlpnProtos,
                     size_t alpnProtosLen,
                     SSL ** pSslContext )
{
    int status = EXIT_FAILURE, sslStatus = 0, alpnStatus = -1, sslVerifyStatus = 0;
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;
    SSL_CTX * pSslSetup = NULL;

    assert( tcpSocket >= 0 );

    /* Setup for creating a TLS client. */
    pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        /* Setup authentication. */
        sslStatus = readCredentials( pSslSetup,
                                     ROOT_CA_CERT_PATH,
                                     CLIENT_CERT_PATH,
                                     CLIENT_PRIVATE_KEY_PATH );

        if( sslStatus != 1 )
        {
            LogError( ( "Setting up credentials failed." ) );
        }
    }
    else
    {
        LogError( ( "Failed setting up a TLS client." ) );
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

            if( sslStatus != 1 )
            {
                LogError( ( "Failed to set the socket fd to SSL context." ) );
            }
        }
        else
        {
            LogError( ( "Failed to create a new SSL context." ) );
            sslStatus = 0;
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pAlpnProtos != NULL ) && ( alpnProtosLen > 0 ) )
    {
        sslStatus = -1;

        if( AWS_MQTT_PORT != 443 )
        {
            LogError( ( "AWS_MQTT_PORT must be set to 443 to use ALPN." ) );
        }
        else
        {
            alpnStatus = SSL_set_alpn_protos( *pSslContext,
                                              ( unsigned char * ) pAlpnProtos,
                                              ( unsigned int ) alpnProtosLen );
        }

        if( alpnStatus != 0 )
        {
            LogError( ( "SSL_set_alpn_protos failed to set ALPN protos. %s",
                        pAlpnProtos ) );
        }
        else
        {
            sslStatus = 1;
        }
    }

    /* Perform the TLS handshake. */
    if( sslStatus == 1 )
    {
        sslStatus = SSL_connect( *pSslContext );

        if( sslStatus != 1 )
        {
            LogError( ( "Failed to perform TLS handshake." ) );
        }
    }

    /* Verify the peer certificate. */
    if( sslStatus == 1 )
    {
        sslVerifyStatus = SSL_get_verify_result( *pSslContext );

        if( sslVerifyStatus != X509_V_OK )
        {
            sslStatus = 0;
            LogError( ( "Verifying the peer certificate failed. " ) );
        }
    }

    /* Clean up on error. */
    if( ( sslStatus == 0 ) && ( pSslSetup != NULL ) )
    {
        SSL_free( *pSslContext );
        *pSslContext = NULL;
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
    if( sslStatus != 1 )
    {
        LogError( ( "Failed to establish a TLS connection to %.*s.",
                    AWS_IOT_ENDPOINT_LENGTH,
                    AWS_IOT_ENDPOINT ) );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection to %.*s.\n\n",
                   AWS_IOT_ENDPOINT_LENGTH,
                   AWS_IOT_ENDPOINT ) );
        status = EXIT_SUCCESS;
    }

    return status;
}

/*-----------------------------------------------------------*/

static int32_t transportSend( NetworkContext_t pNetworkContext,
                              const void * pMessage,
                              size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor;

    fileDescriptor.events = POLLOUT;
    fileDescriptor.revents = 0;
    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pNetworkContext );

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pNetworkContext, pMessage, bytesToSend );
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

static int32_t transportRecv( NetworkContext_t pNetworkContext,
                              void * pBuffer,
                              size_t bytesToRecv )
{
    int32_t bytesReceived = 0;
    int pollStatus = -1, bytesAvailableToRead = 0;
    struct pollfd fileDescriptor;

    fileDescriptor.events = POLLIN | POLLPRI;
    fileDescriptor.revents = 0;
    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pNetworkContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pNetworkContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );
    }

    /* Read data if it was already pending or if it became available during
     * polling. */
    if( ( bytesAvailableToRead > 0 ) || ( pollStatus > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pNetworkContext, pBuffer, bytesToRecv );
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
    int index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( pIndex != NULL );

    for( index = 0; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        /* A free index is marked by invalid packet id.
         * Check if the the index has a free slot. */
        if( outgoingPublishPackets[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            status = EXIT_SUCCESS;
            break;
        }
    }

    /* Copy the available index into the output param. */
    *pIndex = index;

    return status;
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

static void cleanupOutgoingPublishes()
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

static int handlePublishResend( MQTTContext_t * pContext )
{
    int status = EXIT_SUCCESS;
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
            mqttStatus = MQTT_Publish( pContext,
                                       &outgoingPublishPackets[ index ].pubInfo,
                                       outgoingPublishPackets[ index ].packetId );

            if( mqttStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %u.",
                            outgoingPublishPackets[ index ].packetId,
                            mqttStatus ) );
                status = EXIT_FAILURE;
                break;
            }
            else
            {
                LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.\n\n",
                           outgoingPublishPackets[ index ].packetId ) );
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo,
                                   uint16_t packetIdentifier )
{
    assert( pPublishInfo != NULL );

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
                LogInfo( ( "PINGRESP received.\n\n" ) );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                LogInfo( ( "PUBACK received for packet id %u.",
                           packetIdentifier ) );
                /* Cleanup publish packet when a PUBACK is received. */
                cleanupOutgoingPublishWithPacketID( packetIdentifier );
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
     * from network. Network context is SSL context.*/
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

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
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
     * and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
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
    MQTTStatus_t mqttStatus;
    uint8_t publishIndex = MAX_OUTGOING_PUBLISHES;

    assert( pContext != NULL );

    /* Get the next free index for the outgoing publish. All QoS1 outgoing
     * publishes are stored until a PUBACK is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBACK. */
    status = getNextFreeIndexForOutgoingPublishes( &publishIndex );

    if( status == EXIT_FAILURE )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message.\n\n" ) );
    }
    else
    {
        /* This example publishes to only one topic and uses QOS1. */
        outgoingPublishPackets[ publishIndex ].pubInfo.qos = MQTTQoS1;
        outgoingPublishPackets[ publishIndex ].pubInfo.pTopicName = MQTT_EXAMPLE_TOPIC;
        outgoingPublishPackets[ publishIndex ].pubInfo.topicNameLength = MQTT_EXAMPLE_TOPIC_LENGTH;
        outgoingPublishPackets[ publishIndex ].pubInfo.pPayload = MQTT_EXAMPLE_MESSAGE;
        outgoingPublishPackets[ publishIndex ].pubInfo.payloadLength = MQTT_EXAMPLE_MESSAGE_LENGTH;

        /* Get a new packet id. */
        outgoingPublishPackets[ publishIndex ].packetId = MQTT_GetPacketId( pContext );

        /* Send PUBLISH packet. */
        mqttStatus = MQTT_Publish( pContext,
                                   &outgoingPublishPackets[ publishIndex ].pubInfo,
                                   outgoingPublishPackets[ publishIndex ].packetId );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.",
                        mqttStatus ) );
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
 * it uses QOS1 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBACK
 * are resent in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBACK is received.
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
     * to the MQTT broker as specified in AWS_IOT_ENDPOINT and AWS_MQTT_PORT in
     * the demo_config.h file. */
    LogInfo( ( "Creating a TCP connection to %.*s:%d.",
               AWS_IOT_ENDPOINT_LENGTH,
               AWS_IOT_ENDPOINT,
               AWS_MQTT_PORT ) );
    status = connectToServer( AWS_IOT_ENDPOINT, AWS_MQTT_PORT, &tcpSocket );

    /* Establish TLS connection on top of TCP connection. */
    if( status == EXIT_SUCCESS )
    {
        LogInfo( ( "Performing TLS handshake on top of the TCP connection." ) );

        if( AWS_MQTT_PORT == 443 )
        {
            /* Pass the ALPN protocol name depending on the port being used.
             * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
             * in the link below.
             * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
             */
            status = tlsSetup( tcpSocket,
                               ALPN_PROTOCOL_NAME,
                               ALPN_PROTOCOL_NAME_LENGTH,
                               &pSslContext );
        }
        else if( AWS_MQTT_PORT == 8883 )
        {
            status = tlsSetup( tcpSocket,
                               NULL,
                               0,
                               &pSslContext );
        }
        else
        {
            LogError( ( "AWS IoT Core does not support MQTT through port %d",
                        AWS_MQTT_PORT ) );
            status = EXIT_FAILURE;
        }
    }

    /* Establish MQTT session on top of TCP+TLS connection. */
    if( status == EXIT_SUCCESS )
    {
        /* Sends an MQTT Connect packet over the already connected TCP socket
         * tcpSocket, and waits for connection acknowledgment (CONNACK) packet. */
        LogInfo( ( "Creating an MQTT connection to %.*s.",
                   AWS_IOT_ENDPOINT_LENGTH,
                   AWS_IOT_ENDPOINT ) );
        status = establishMqttSession( &context, pSslContext, false, &sessionPresent );

        if( status == EXIT_SUCCESS )
        {
            /* Keep a flag for indicating if MQTT session is established. This
             * flag will mark that an MQTT DISCONNECT has to be sent at the end
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
            cleanupOutgoingPublishes();
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in MQTT_EXAMPLE_TOPIC at the top of this file by sending a
         * subscribe packet. This client will then publish to the same topic it
         * subscribed to, so it will expect all the messages it sends to the broker
         * to be sent back to it from the broker. This demo uses QOS1 in Subscribe,
         * therefore, the Publish messages received from the broker will have QOS1. */
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
        /* Publish messages with QOS1, receive incoming messages and
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
