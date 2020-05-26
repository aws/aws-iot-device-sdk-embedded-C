#include <string.h>
#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "mqtt.h"

#include "mock_mqtt_lightweight.h"
#include "mock_mqtt_state.h"

/**
 * @brief A valid starting packet ID per MQTT spec. Start from 1.
 */
#define MQTT_FIRST_VALID_PACKET_ID          ( 1 )

/**
 * @brief A PINGREQ packet is always 2 bytes in size, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_PINGREQ_SIZE            ( 2U )

/**
 * @brief A packet type not handled by MQTT_ProcessLoop.
 */
#define MQTT_PACKET_TYPE_INVALID            ( 0U )

/**
 * @brief Number of milliseconds in a second.
 */
#define MQTT_ONE_SECOND_TO_MS               ( 1000U )

/**
 * @brief Length of the MQTT network buffer.
 */
#define MQTT_TEST_BUFFER_LENGTH             ( 128 )

/**
 * @brief Sample keep-alive interval that should be greater than 0.
 */
#define MQTT_SAMPLE_KEEPALIVE_INTERVAL_S    ( 1U )

/**
 * @brief Length of time spent for single test case with
 * multiple iterations spent in the process loop for coverage.
 */
#define MQTT_SAMPLE_TIMEOUT_MS              ( 1U )

/**
 * @brief Zero timeout in the process loop implies one iteration.
 */
#define MQTT_NO_TIMEOUT_MS                  ( 0U )

/**
 * @brief Sample length of remaining serialized data.
 */
#define MQTT_SAMPLE_REMAINING_LENGTH        ( 64 )

/**
 * @brief Subtract this value from max value of global entry time
 * for the timer overflow test.
 */
#define MQTT_OVERFLOW_OFFSET                ( 3 )

/**
 * @brief Subtract this value from max value of global entry time
 * for the timer overflow test.
 */
#define MQTT_TIMER_CALLS_PER_ITERATION      ( 3 )

/**
 * @brief Timeout for the timer overflow test.
 */
#define MQTT_TIMER_OVERFLOW_TIMEOUT_MS      ( 10 )


/**
 * @brief The packet type to be received by the process loop.
 * IMPORTANT: Make sure this is set before calling expectProcessLoopCalls(...).
 */
static uint8_t currentPacketType = MQTT_PACKET_TYPE_INVALID;

/**
 * @brief The return value of modifyIncomingPacket(...) CMock callback that
 * replaces a call to MQTT_GetIncomingPacketTypeAndLength.
 * IMPORTANT: Make sure this is set before calling expectProcessLoopCalls(...).
 */
static MQTTStatus_t modifyIncomingPacketStatus = MQTTSuccess;

/**
 * @brief Time at the beginning of each test. Note that this is not updated with
 * a real clock. Instead, we simply increment this variable.
 */
static uint32_t globalEntryTime = 0;

/**
 * @brief A static buffer used by the MQTT library for storing packet data.
 */
static uint8_t mqttBuffer[ MQTT_TEST_BUFFER_LENGTH ] = { 0 };

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    memset( ( void * ) mqttBuffer, 0x0, sizeof( mqttBuffer ) );
    globalEntryTime = 0;
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ========================================================================== */

/**
 * @brief Mock successful transport send, and write data into buffer for
 * verification.
 */
static int32_t mockSend( MQTTNetworkContext_t context,
                         const void * pMessage,
                         size_t bytesToSend )
{
    const uint8_t * buffer = ( const uint8_t * ) pMessage;
    /* Treat network context as pointer to buffer for mocking. */
    uint8_t * mockNetwork = ( *( uint8_t ** ) context );
    size_t bytesSent = 0;

    while( bytesSent++ < bytesToSend )
    {
        /* Write single byte and advance buffer. */
        *mockNetwork++ = *buffer++;
    }

    /* Move stream by bytes sent. */
    ( *( uint8_t ** ) context ) = mockNetwork;

    return bytesToSend;
}

/**
 * @brief Initialize pNetworkBuffer using static buffer.
 *
 * @param[in] pNetworkBuffer Network buffer provided for the context.
 */
static void setupNetworkBuffer( MQTTFixedBuffer_t * const pNetworkBuffer )
{
    pNetworkBuffer->pBuffer = mqttBuffer;
    pNetworkBuffer->size = MQTT_TEST_BUFFER_LENGTH;
}

/**
 * @brief Mocked MQTT event callback.
 */
static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo )
{
    ( void ) pContext;
    ( void ) pPacketInfo;
    ( void ) packetIdentifier;
    ( void ) pPublishInfo;
}

/**
 * @brief A mocked timer query function that increments on every call. This
 * guarantees that only a single iteration runs in the ProcessLoop for ease
 * of testing.
 */
static uint32_t getTime( void )
{
    return globalEntryTime++;
}

/**
 * @brief Mocked successful transport send.
 */
static int32_t transportSendSuccess( MQTTNetworkContext_t pContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;
    return bytesToWrite;
}

/**
 * @brief Mocked failed transport send.
 */
static int32_t transportSendFailure( MQTTNetworkContext_t pContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;
    ( void ) bytesToWrite;
    return -1;
}

/**
 * @brief Mocked successful transport read.
 */
static int32_t transportRecvSuccess( MQTTNetworkContext_t pContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;
    return bytesToRead;
}

/**
 * @brief Mocked failed transport read.
 */
static int32_t transportRecvFailure( MQTTNetworkContext_t pContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;
    ( void ) bytesToRead;
    return -1;
}

/**
 * @brief Mocked failed transport read.
 */
static int32_t transportRecvOneByte( MQTTNetworkContext_t pContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;
    return 1;
}

/**
 * @brief Initialize the transport interface with the mocked functions for
 * send and receive.
 */
static void setupTransportInterface( MQTTTransportInterface_t * pTransport )
{
    pTransport->networkContext = 0;
    pTransport->send = transportSendSuccess;
    pTransport->recv = transportRecvSuccess;
}

/**
 * @brief Initialize our event and time callback with the mocked functions
 * defined for the purposes this test.
 */
static void setupCallbacks( MQTTApplicationCallbacks_t * pCallbacks )
{
    pCallbacks->appCallback = eventCallback;
    pCallbacks->getTime = getTime;
}

/* Mocked MQTT_GetIncomingPacketTypeAndLength callback that modifies pIncomingPacket
 * to get full coverage on handleIncomingAck by setting the type to CONNECT. */
static MQTTStatus_t modifyIncomingPacket( MQTTTransportRecvFunc_t readFunc,
                                          MQTTNetworkContext_t networkContext,
                                          MQTTPacketInfo_t * pIncomingPacket,
                                          int cmock_num_calls )
{
    /* Remove unused parameter warnings. */
    ( void ) readFunc;
    ( void ) networkContext;
    ( void ) cmock_num_calls;

    pIncomingPacket->type = currentPacketType;
    pIncomingPacket->remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;
    return modifyIncomingPacketStatus;
}

/**
 * @brief This helper function is used to expect any calls from the process loop
 * to mocked functions belonging to an external header file. Its parameters
 * are used to provide return values for these mocked functions.
 */
static void expectProcessLoopCalls( MQTTContext_t * const pContext,
                                    MQTTStatus_t deserializeStatus,
                                    MQTTPublishState_t stateAfterDeserialize,
                                    MQTTStatus_t serializeStatus,
                                    MQTTPublishState_t stateAfterSerialize,
                                    MQTTStatus_t processLoopStatus,
                                    bool incomingPublish )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };
    size_t pingreqSize = MQTT_PACKET_PINGREQ_SIZE;
    bool expectMoreCalls = true;

    MQTT_GetIncomingPacketTypeAndLength_Stub( modifyIncomingPacket );

    /* More calls are expected only with the following packet types. */
    if( ( currentPacketType != MQTT_PACKET_TYPE_PUBLISH ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBACK ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBREC ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBREL ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PUBCOMP ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_PINGRESP ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_SUBACK ) &&
        ( currentPacketType != MQTT_PACKET_TYPE_UNSUBACK ) )
    {
        expectMoreCalls = false;
    }

    /* When no data is available, the process loop tries to send a PINGREQ. */
    if( modifyIncomingPacketStatus == MQTTNoDataAvailable )
    {
        if( ( pContext->waitingForPingResp == false ) &&
            ( pContext->keepAliveIntervalSec != 0U ) )
        {
            MQTT_GetPingreqPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
            /* Replace pointer parameter being passed to the method. */
            MQTT_GetPingreqPacketSize_ReturnThruPtr_pPacketSize( &pingreqSize );
            MQTT_SerializePingreq_ExpectAnyArgsAndReturn( serializeStatus );
        }

        expectMoreCalls = false;
    }

    /* Deserialize based on the packet type (PUB or ACK) being received. */
    if( expectMoreCalls )
    {
        if( incomingPublish )
        {
            MQTT_DeserializePublish_ExpectAnyArgsAndReturn( deserializeStatus );
        }
        else
        {
            MQTT_DeserializeAck_ExpectAnyArgsAndReturn( deserializeStatus );
        }

        if( ( deserializeStatus != MQTTSuccess ) ||
            ( currentPacketType == MQTT_PACKET_TYPE_PINGRESP ) ||
            ( currentPacketType == MQTT_PACKET_TYPE_SUBACK ) ||
            ( currentPacketType == MQTT_PACKET_TYPE_UNSUBACK ) )
        {
            expectMoreCalls = false;
        }
    }

    /* Update state based on the packet type (PUB or ACK) being received. */
    if( expectMoreCalls )
    {
        if( incomingPublish )
        {
            MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( stateAfterDeserialize );
        }
        else
        {
            MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( stateAfterDeserialize );
        }

        if( stateAfterDeserialize == MQTTPublishDone )
        {
            expectMoreCalls = false;
        }
    }

    /* Serialize the packet to be sent in response to the received packet. */
    if( expectMoreCalls )
    {
        MQTT_SerializeAck_ExpectAnyArgsAndReturn( serializeStatus );

        if( serializeStatus != MQTTSuccess )
        {
            expectMoreCalls = false;
        }
    }

    /* Update the state based on the sent packet. */
    if( expectMoreCalls )
    {
        MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( stateAfterSerialize );
    }

    /* Expect the above calls when running MQTT_ProcessLoop. */
    mqttStatus = MQTT_ProcessLoop( pContext, MQTT_NO_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( processLoopStatus, mqttStatus );

    /* Any final assertions to end the test. */
    if( mqttStatus == MQTTSuccess )
    {
        if( currentPacketType == MQTT_PACKET_TYPE_PUBLISH )
        {
            TEST_ASSERT_TRUE( pContext->controlPacketSent );
        }

        if( currentPacketType == MQTT_PACKET_TYPE_PINGRESP )
        {
            TEST_ASSERT_FALSE( pContext->waitingForPingResp );
        }
    }
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_Init is able to update the context object correctly.
 */
void test_MQTT_Init_Happy_Path( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL( MQTTNotConnected, context.connectStatus );
    TEST_ASSERT_EQUAL( MQTT_FIRST_VALID_PACKET_ID, context.nextPacketId );
    /* These Unity assertions take pointers and compare their contents. */
    TEST_ASSERT_EQUAL_MEMORY( &transport, &context.transportInterface, sizeof( transport ) );
    TEST_ASSERT_EQUAL_MEMORY( &callbacks, &context.callbacks, sizeof( callbacks ) );
    TEST_ASSERT_EQUAL_MEMORY( &networkBuffer, &context.networkBuffer, sizeof( networkBuffer ) );
}

/**
 * @brief Test that any NULL parameter causes MQTT_Init to return MQTTBadParameter.
 */
void test_MQTT_Init_Invalid_Params( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    /* Check that MQTTBadParameter is returned if any NULL parameters are passed. */
    mqttStatus = MQTT_Init( NULL, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTT_Init( &context, NULL, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTT_Init( &context, &transport, NULL, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/* ========================================================================== */

/**
 * @brief Test MQTT_Connect, except for receiving the CONNACK.
 */
void test_MQTT_Connect_sendConnect( void )
{
    MQTTContext_t mqttContext;
    MQTTConnectInfo_t connectInfo;
    MQTTPublishInfo_t willInfo;
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    MQTTPacketInfo_t incomingPacket;
    size_t remainingLength, packetSize;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );

    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );

    /* Check parameters */
    status = MQTT_Connect( NULL, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
    status = MQTT_Connect( &mqttContext, NULL, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, NULL );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Empty connect info fails. */
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTBadParameter );
    memset( ( void * ) &connectInfo, 0x0, sizeof( connectInfo ) );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    connectInfo.pClientIdentifier = MQTT_CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = sizeof( MQTT_CLIENT_IDENTIFIER ) - 1;

    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_SerializeConnect_ExpectAnyArgsAndReturn( MQTTNoMemory );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTNoMemory, status );

    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );

    /* Transport send failed when sending CONNECT. */

    /* Choose 10 bytes variable header + 1 byte payload for the remaining
     * length of the CONNECT. The packet size needs to be nonzero for this test
     * as that is the amount of bytes used in the call to send the packet. */
    packetSize = 13;
    remainingLength = 11;
    mqttContext.transportInterface.send = transportSendFailure;
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreArg_pPacketSize();
    MQTT_GetConnectPacketSize_IgnoreArg_pRemainingLength();
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );

    /* Send the CONNECT successfully. This provides branch coverage for sendPacket. */
    mqttContext.transportInterface.send = transportSendSuccess;
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pPacketSize( &packetSize );
    MQTT_GetConnectPacketSize_ReturnThruPtr_pRemainingLength( &remainingLength );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTRecvFailed );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );
}

/**
 * @brief Test CONNACK reception in MQTT_Connect.
 */
void test_MQTT_Connect_receiveConnack( void )
{
    MQTTContext_t mqttContext;
    MQTTConnectInfo_t connectInfo;
    uint32_t timeout = 0;
    bool sessionPresent;
    MQTTStatus_t status;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    MQTTPacketInfo_t incomingPacket;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );
    transport.recv = transportRecvFailure;

    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );

    /* Everything before receiving the CONNACK should succeed. */
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );

    /* Nothing received from transport interface. Set timeout to 2 for branch coverage. */
    timeout = 2;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTNoDataAvailable );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTNoDataAvailable, status );

    /* Did not receive a CONNACK. */
    incomingPacket.type = MQTT_PACKET_TYPE_PINGRESP;
    incomingPacket.remainingLength = 0;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );

    /* Transport receive failure when receiving rest of packet. */
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    timeout = 2;
    mqttContext.transportInterface.recv = transportRecvFailure;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Bad response when deserializing CONNACK. */
    mqttContext.transportInterface.recv = transportRecvSuccess;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_ExpectAnyArgsAndReturn( MQTTBadResponse );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTBadResponse, status );
}

/**
 * @brief Test error cases for MQTT_Connect when a timeout occurs or the packet
 * needs to be discarded in MQTT_Connect.
 */
void test_MQTT_Connect_partial_receive()
{
    MQTTContext_t mqttContext;
    MQTTConnectInfo_t connectInfo;
    uint32_t timeout = 0;
    bool sessionPresent;
    MQTTStatus_t status;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    MQTTPacketInfo_t incomingPacket;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );
    transport.recv = transportRecvOneByte;

    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );

    /* Everything before receiving the CONNACK should succeed. */
    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;

    /* Not enough time to receive entire packet, for branch coverage. */
    timeout = 1;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    timeout = 10;

    /* Not enough space for packet, discard it. */
    mqttContext.networkBuffer.size = 2;
    incomingPacket.remainingLength = 3;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTNoDataAvailable, status );

    /* Timeout while discarding packet. */
    incomingPacket.remainingLength = 20;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );

    /* Receive failure while discarding packet. */
    mqttContext.transportInterface.recv = transportRecvFailure;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTRecvFailed, status );
}

/**
 * @brief Test success case for MQTT_Connect().
 */
void test_MQTT_Connect_happy_path()
{
    MQTTContext_t mqttContext;
    MQTTConnectInfo_t connectInfo;
    MQTTPublishInfo_t willInfo;
    uint32_t timeout = 2;
    bool sessionPresent;
    MQTTStatus_t status;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    MQTTPacketInfo_t incomingPacket;
    size_t remainingLength, packetSize;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );

    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );

    MQTT_SerializeConnect_IgnoreAndReturn( MQTTSuccess );
    MQTT_GetConnectPacketSize_IgnoreAndReturn( MQTTSuccess );

    /* Success. */
    incomingPacket.type = MQTT_PACKET_TYPE_CONNACK;
    incomingPacket.remainingLength = 2;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    MQTT_DeserializeAck_IgnoreAndReturn( MQTTSuccess );
    status = MQTT_Connect( &mqttContext, &connectInfo, NULL, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );

    /* With non-NULL Will. */
    mqttContext.connectStatus = MQTTNotConnected;
    willInfo.pTopicName = "test";
    willInfo.topicNameLength = 4;
    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
    status = MQTT_Connect( &mqttContext, &connectInfo, &willInfo, timeout, &sessionPresent );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
    TEST_ASSERT_EQUAL_INT( MQTTConnected, mqttContext.connectStatus );
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_Publish works as intended.
 */
void test_MQTT_Publish( void )
{
    MQTTContext_t mqttContext;
    MQTTPublishInfo_t publishInfo;
    uint16_t packetId;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    MQTTStatus_t status;
    size_t headerSize;

    const uint16_t PACKET_ID = 1;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );
    transport.send = transportSendFailure;

    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    memset( ( void * ) &publishInfo, 0x0, sizeof( publishInfo ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );

    /* Verify parameters. */
    status = MQTT_Publish( NULL, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
    status = MQTT_Publish( &mqttContext, NULL, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );
    publishInfo.qos = MQTTQoS1;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Bad Parameter when getting packet size. */
    publishInfo.qos = MQTTQoS0;
    MQTT_GetPublishPacketSize_ExpectAnyArgsAndReturn( MQTTBadParameter );
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Always return success from now on. */
    MQTT_GetPublishPacketSize_IgnoreAndReturn( MQTTSuccess );

    MQTT_SerializePublishHeader_ExpectAnyArgsAndReturn( MQTTNoMemory );
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTNoMemory, status );

    /* The transport interface will fail. */
    MQTT_SerializePublishHeader_ExpectAnyArgsAndReturn( MQTTSuccess );

    /* We need sendPacket to be called with at least 1 byte to send, so that
     * it can return failure. This argument is the output of serializing the
     * publish header. */
    headerSize = 1;
    MQTT_SerializePublishHeader_ReturnThruPtr_pHeaderSize( &headerSize );
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );

    /* We can ignore this now since MQTT_Publish initializes the header size to
     * 0, so its initial send returns success (since 0 bytes are sent). */
    MQTT_SerializePublishHeader_IgnoreAndReturn( MQTTSuccess );
    publishInfo.pPayload = "Test";
    publishInfo.payloadLength = 4;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSendFailed, status );

    mqttContext.transportInterface.send = transportSendSuccess;
    status = MQTT_Publish( &mqttContext, &publishInfo, 0 );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );

    /* Now for non zero QoS, which uses state engine. */
    publishInfo.qos = MQTTQoS2;
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTStateNull );
    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    publishInfo.qos = MQTTQoS1;
    MQTT_ReserveState_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTPublishSend );
    status = MQTT_Publish( &mqttContext, &publishInfo, PACKET_ID );
    TEST_ASSERT_EQUAL_INT( MQTTSuccess, status );
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_Disconnect works as intended.
 */
void test_MQTT_Disconnect( void )
{
    MQTTContext_t mqttContext;
    MQTTStatus_t status;
    uint8_t buffer[ 10 ];
    uint8_t * bufPtr = buffer;
    MQTTNetworkContext_t networkContext = ( MQTTNetworkContext_t ) &bufPtr;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    size_t disconnectSize = 2;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );
    transport.networkContext = networkContext;
    transport.recv = transportRecvSuccess;
    transport.send = transportSendFailure;

    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );
    mqttContext.connectStatus = MQTTConnected;

    /* Verify parameters. */
    status = MQTT_Disconnect( NULL );
    TEST_ASSERT_EQUAL_INT( MQTTBadParameter, status );

    /* Send failure. */
    MQTT_GetDisconnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetDisconnectPacketSize_ReturnThruPtr_pPacketSize( &disconnectSize );
    MQTT_SerializeDisconnect_ExpectAnyArgsAndReturn( MQTTSuccess );
    status = MQTT_Disconnect( &mqttContext );
    TEST_ASSERT_EQUAL( MQTTSendFailed, status );

    /* Successful send. */
    mqttContext.transportInterface.send = mockSend;
    MQTT_GetDisconnectPacketSize_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_GetDisconnectPacketSize_ReturnThruPtr_pPacketSize( &disconnectSize );
    MQTT_SerializeDisconnect_ExpectAnyArgsAndReturn( MQTTSuccess );
    /* Write a disconnect packet into the buffer. */
    mqttBuffer[ 0 ] = MQTT_PACKET_TYPE_DISCONNECT;
    status = MQTT_Disconnect( &mqttContext );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTNotConnected, mqttContext.connectStatus );
    TEST_ASSERT_EQUAL_MEMORY( mqttBuffer, buffer, 2 );
}

/* ========================================================================== */

/**
 * @brief Test that MQTT_GetPacketId works as intended.
 */
void test_MQTT_GetPacketId( void )
{
    MQTTContext_t mqttContext;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    uint16_t packetId;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );
    setupNetworkBuffer( &networkBuffer );
    memset( ( void * ) &mqttContext, 0x0, sizeof( mqttContext ) );
    MQTT_Init( &mqttContext, &transport, &callbacks, &networkBuffer );

    /* Verify parameters. */
    packetId = MQTT_GetPacketId( NULL );
    TEST_ASSERT_EQUAL_INT( 0, packetId );

    packetId = MQTT_GetPacketId( &mqttContext );
    TEST_ASSERT_EQUAL_INT( 1, packetId );
    TEST_ASSERT_EQUAL_INT( 2, mqttContext.nextPacketId );

    mqttContext.nextPacketId = UINT16_MAX;
    packetId = MQTT_GetPacketId( &mqttContext );
    TEST_ASSERT_EQUAL_INT( UINT16_MAX, packetId );
    TEST_ASSERT_EQUAL_INT( 1, mqttContext.nextPacketId );
}

/**
 * @brief Test that NULL pContext causes MQTT_ProcessLoop to return MQTTBadParameter.
 */
void test_MQTT_ProcessLoop_Invalid_Params( void )
{
    MQTTStatus_t mqttStatus = MQTT_ProcessLoop( NULL, MQTT_NO_TIMEOUT_MS );

    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Happy_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Assume QoS = 1 so that a PUBACK will be sent after receiving PUBLISH. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPubAckSend,
                            MQTTSuccess, MQTTPublishDone,
                            MQTTSuccess, true );

    /* Assume QoS = 2 so that a PUBREC will be sent after receiving PUBLISH. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPubRecSend,
                            MQTTSuccess, MQTTPubRelPending,
                            MQTTSuccess, true );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingPublish(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleIncomingPublish_Error_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Verify that an error is propagated when deserialization fails by returning
     * MQTTBadResponse. Any parameters beyond that are actually irrelevant
     * because they are only used as return values for non-expected calls. */
    currentPacketType = MQTT_PACKET_TYPE_PUBLISH;
    expectProcessLoopCalls( &context, MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, true );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingAck(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleIncomingAck_Happy_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Mock the receiving of a PUBACK packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBACK;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPublishDone,
                            MQTTSuccess, MQTTPublishDone,
                            MQTTSuccess, false );

    /* Mock the receiving of a PUBREC packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREC;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPubRelSend,
                            MQTTSuccess, MQTTPubCompPending,
                            MQTTSuccess, false );

    /* Mock the receiving of a PUBREL packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREL;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPubCompSend,
                            MQTTSuccess, MQTTPublishDone,
                            MQTTSuccess, false );

    /* Mock the receiving of a PUBCOMP packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PUBCOMP;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPublishDone,
                            MQTTSuccess, MQTTPublishDone,
                            MQTTSuccess, false );

    /* Mock the receiving of a PINGRESP packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );

    /* Mock the receiving of a SUBACK packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_SUBACK;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );

    /* Mock the receiving of an UNSUBACK packet type and expect the appropriate
     * calls made from the process loop. */
    currentPacketType = MQTT_PACKET_TYPE_UNSUBACK;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleIncomingAck(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleIncomingAck_Error_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    modifyIncomingPacketStatus = MQTTSuccess;

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving an unknown packet type. */
    currentPacketType = MQTT_PACKET_TYPE_INVALID;
    expectProcessLoopCalls( &context, MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, false );

    /* Verify that MQTTSendFailed is propagated when receiving a PUBREC
     * then failing when serializing a PUBREL to send in response. */
    currentPacketType = MQTT_PACKET_TYPE_PUBREC;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPubRelSend,
                            MQTTNoMemory, MQTTStateNull,
                            MQTTSendFailed, false );

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving a PUBACK. */
    currentPacketType = MQTT_PACKET_TYPE_PUBACK;
    expectProcessLoopCalls( &context, MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, false );

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving a PINGRESP. */
    currentPacketType = MQTT_PACKET_TYPE_PINGRESP;
    expectProcessLoopCalls( &context, MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, false );

    /* Verify that MQTTBadResponse is propagated when deserialization fails upon
     * receiving a SUBACK. */
    currentPacketType = MQTT_PACKET_TYPE_SUBACK;
    expectProcessLoopCalls( &context, MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, MQTTStateNull,
                            MQTTBadResponse, false );

    /* Verify that MQTTIllegalState is returned if MQTT_UpdateStateAck(...)
     * provides an unknown state such as MQTTStateNull to sendPublishAcks(...). */
    currentPacketType = MQTT_PACKET_TYPE_PUBREC;
    expectProcessLoopCalls( &context, MQTTSuccess, MQTTPubRelSend,
                            MQTTSuccess, MQTTStateNull,
                            MQTTIllegalState, false );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning successfully.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Happy_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_ONE_SECOND_TO_MS;

    /* Coverage for the branch path where keep alive interval is 0. */
    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.waitingForPingResp = false;
    context.keepAliveIntervalSec = 0;
    expectProcessLoopCalls( &context, MQTTStateNull, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );

    /* Coverage for the branch path where keep alive interval is greater than 0,
     * and the interval has expired. */
    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.waitingForPingResp = true;
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTime = getTime();
    expectProcessLoopCalls( &context, MQTTStateNull, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );

    /* Coverage for the branch path where PINGRESP timeout interval hasn't expired. */
    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.waitingForPingResp = true;
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTime = 0;
    context.pingReqSendTimeMs = MQTT_ONE_SECOND_TO_MS;
    context.pingRespTimeoutMs = MQTT_ONE_SECOND_TO_MS;
    expectProcessLoopCalls( &context, MQTTStateNull, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );

    /* Coverage for the branch path where a PINGRESP hasn't been sent out yet. */
    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.waitingForPingResp = false;
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.lastPacketTime = 0;
    expectProcessLoopCalls( &context, MQTTStateNull, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTSuccess, false );
}

/**
 * @brief This test case covers all calls to the private method,
 * handleKeepAlive(...),
 * that result in the process loop returning an error.
 */
void test_MQTT_ProcessLoop_handleKeepAlive_Error_Paths( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    modifyIncomingPacketStatus = MQTTNoDataAvailable;
    globalEntryTime = MQTT_ONE_SECOND_TO_MS;

    /* Coverage for the branch path where PING timeout interval hasn't expired. */
    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    context.lastPacketTime = 0;
    context.keepAliveIntervalSec = MQTT_SAMPLE_KEEPALIVE_INTERVAL_S;
    context.waitingForPingResp = true;
    expectProcessLoopCalls( &context, MQTTStateNull, MQTTStateNull,
                            MQTTSuccess, MQTTStateNull,
                            MQTTKeepAliveTimeout, false );
}

/**
 * @brief This test mocks a failing transport receive and runs multiple
 * iterations of the process loop, resulting in returning MQTTRecvFailed.
 */
void test_MQTT_ProcessLoop_Receive_Failed( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTRecvFailed );
    mqttStatus = MQTT_ProcessLoop( &context, MQTT_SAMPLE_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( MQTTRecvFailed, mqttStatus );
}

/**
 * @brief This test mocks a failing transport receive and runs multiple
 * iterations of the process loop, resulting in returning MQTTRecvFailed.
 * This allows us to have full branch and line coverage.
 */
void test_MQTT_ProcessLoop_Timer_Overflow( void )
{
    MQTTStatus_t mqttStatus;
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;
    MQTTPacketInfo_t incomingPacket = { 0 };
    uint8_t i = 0;
    uint8_t numIterations = ( MQTT_TIMER_OVERFLOW_TIMEOUT_MS / MQTT_TIMER_CALLS_PER_ITERATION ) + 1;

    setupTransportInterface( &transport );
    setupCallbacks( &callbacks );

    networkBuffer.size = 1000;
    incomingPacket.type = MQTT_PACKET_TYPE_PUBLISH;
    incomingPacket.remainingLength = MQTT_SAMPLE_REMAINING_LENGTH;

    globalEntryTime = UINT32_MAX - MQTT_OVERFLOW_OFFSET;

    mqttStatus = MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Verify that we run the expected number of iterations despite overflowing. */
    for( ; i < numIterations; i++ )
    {
        MQTT_GetIncomingPacketTypeAndLength_ExpectAnyArgsAndReturn( MQTTSuccess );
        MQTT_GetIncomingPacketTypeAndLength_ReturnThruPtr_pIncomingPacket( &incomingPacket );
        /* Assume QoS = 1 so that a PUBACK will be sent after receiving PUBLISH. */
        MQTT_DeserializePublish_ExpectAnyArgsAndReturn( MQTTSuccess );
        MQTT_UpdateStatePublish_ExpectAnyArgsAndReturn( MQTTPubAckSend );
        MQTT_SerializeAck_ExpectAnyArgsAndReturn( MQTTSuccess );
        MQTT_UpdateStateAck_ExpectAnyArgsAndReturn( MQTTPublishDone );
    }

    mqttStatus = MQTT_ProcessLoop( &context, MQTT_TIMER_OVERFLOW_TIMEOUT_MS );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}
