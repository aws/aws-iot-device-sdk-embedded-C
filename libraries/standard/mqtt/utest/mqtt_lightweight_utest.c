#include <string.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "mqtt_lightweight.h"

/**
 * @brief MQTT protocol version 3.1.1.
 */
#define MQTT_VERSION_3_1_1               ( ( uint8_t ) 4U )

/**
 * @brief Test-defined macro for MQTT username.
 */
#define MQTT_TEST_USERNAME               "username"
#define MQTT_TEST_USERNAME_LEN           sizeof( MQTT_TEST_USERNAME ) - 1

/**
 * @brief Test-defined macro for MQTT password.
 */
#define MQTT_TEST_PASSWORD               "password"
#define MQTT_TEST_PASSWORD_LEN           sizeof( MQTT_TEST_PASSWORD ) - 1

/**
 * @brief Test-defined macro for MQTT topic.
 */
#define MQTT_TEST_TOPIC                  "topic"
#define MQTT_TEST_TOPIC_LEN              sizeof( MQTT_TEST_TOPIC ) - 1

/**
 * @brief Length of the client identifier.
 */
#define CLIENT_IDENTIFIER_LEN            sizeof( CLIENT_IDENTIFIER ) - 1

/* MQTT CONNECT flags. */
#define MQTT_CONNECT_FLAG_CLEAN          ( 1 )            /**< @brief Clean session. */
#define MQTT_CONNECT_FLAG_WILL           ( 2 )            /**< @brief Will present. */
#define MQTT_CONNECT_FLAG_WILL_QOS1      ( 3 )            /**< @brief Will QoS 1. */
#define MQTT_CONNECT_FLAG_WILL_QOS2      ( 4 )            /**< @brief Will QoS 2. */
#define MQTT_CONNECT_FLAG_WILL_RETAIN    ( 5 )            /**< @brief Will retain. */
#define MQTT_CONNECT_FLAG_PASSWORD       ( 6 )            /**< @brief Password present. */
#define MQTT_CONNECT_FLAG_USERNAME       ( 7 )            /**< @brief User name present. */

/**
 * @brief Set a bit in an 8-bit unsigned integer.
 */
#define UINT8_SET_BIT( x, position )      ( ( x ) = ( uint8_t ) ( ( x ) | ( 0x01U << ( position ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to check.
 * @param[in] position Which bit to check.
 */
#define UINT8_CHECK_BIT( x, position )    ( ( ( x ) & ( 0x01U << ( position ) ) ) == ( 0x01U << ( position ) ) )

/**
 * @brief Get the high byte of a 16-bit unsigned integer.
 */
#define UINT16_HIGH_BYTE( x )             ( ( uint8_t ) ( ( x ) >> 8 ) )

/**
 * @brief Get the low byte of a 16-bit unsigned integer.
 */
#define UINT16_LOW_BYTE( x )              ( ( uint8_t ) ( ( x ) & 0x00ffU ) )

/**
 * @brief Maximum number of bytes in the Remaining Length field is four according
 * to MQTT 3.1.1 spec.
 */
#define MQTT_REMAINING_BUFFER_MAX_LENGTH    ( 4 )

/**
 * @brief Length of the MQTT network buffer.
 */
#define MQTT_TEST_BUFFER_LENGTH             ( 1024 )

static uint8_t remainingLengthBuffer[ MQTT_REMAINING_BUFFER_MAX_LENGTH ] = { 0 };

static uint8_t encodedStringBuffer[ MQTT_TEST_BUFFER_LENGTH ] = { 0 };

static uint8_t mqttBuffer[ MQTT_TEST_BUFFER_LENGTH ] = { 0 };

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp( void )
{
}

/* Called after each test method. */
void tearDown( void )
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

/* =====================  Testing MQTT_SerializeConnect ===================== */

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
 * @brief Initialize pConnectInfo using test-defined macros.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 */
static void setupConnectInfo( MQTTConnectInfo_t * const pConnectInfo )
{
    pConnectInfo->cleanSession = true;
    pConnectInfo->pClientIdentifier = CLIENT_IDENTIFIER;
    pConnectInfo->clientIdentifierLength = CLIENT_IDENTIFIER_LEN;
    pConnectInfo->keepAliveSeconds = 0;
    pConnectInfo->pUserName = MQTT_TEST_USERNAME;
    pConnectInfo->userNameLength = MQTT_TEST_USERNAME_LEN;
    pConnectInfo->pPassword = MQTT_TEST_PASSWORD;
    pConnectInfo->passwordLength = MQTT_TEST_PASSWORD_LEN;
}

/**
 * @brief Initialize pWillInfo using test-defined macros.
 *
 * @param[in] pWillInfo Last Will and Testament.
 */
static void setupWillInfo( MQTTPublishInfo_t * const pWillInfo )
{
    pWillInfo->pPayload = NULL;
    pWillInfo->payloadLength = 0;
    pWillInfo->pTopicName = CLIENT_IDENTIFIER;
    pWillInfo->topicNameLength = CLIENT_IDENTIFIER_LEN;
    pWillInfo->dup = true;
    pWillInfo->qos = MQTTQoS1;
    pWillInfo->retain = true;
}

/**
 * @brief Encode remaining length into pDestination for packet serialization
 * using MQTT v3.1.1 spec.
 *
 * @param[in] pDestination Buffer to write encoded remaining length.
 * @param[in] length Actual Remaining length.
 */
static size_t encodeRemainingLength( uint8_t * pDestination,
                                     size_t length )
{
    uint8_t lengthByte;
    uint8_t * pLengthEnd = NULL;
    size_t remainingLength = length;

    TEST_ASSERT_NOT_NULL( pDestination );

    pLengthEnd = pDestination;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        lengthByte = ( uint8_t ) ( remainingLength % 128U );
        remainingLength = remainingLength / 128U;

        /* Set the high bit of this byte, indicating that there's more data. */
        if( remainingLength > 0U )
        {
            UINT8_SET_BIT( lengthByte, 7 );
        }

        /* Output a single encoded byte. */
        *pLengthEnd = lengthByte;
        pLengthEnd++;
    } while( remainingLength > 0U );

    return ( size_t ) ( pLengthEnd - pDestination );
}

/**
 * @brief Encode UTF-8 string and its length into pDestination for
 * packet serialization.
 *
 * @param[in] pDestination Buffer to write encoded remaining length.
 * @param[in] length Actual Remaining length.
 */
static size_t encodeString( uint8_t * pDestination,
                            const char * source,
                            uint16_t sourceLength )
{
    uint8_t * pBuffer = NULL;

    /* Typecast const char * typed source buffer to const uint8_t *.
     * This is to use same type buffers in memcpy. */
    const uint8_t * pSourceBuffer = ( const uint8_t * ) source;

    TEST_ASSERT_NOT_NULL( pDestination );

    pBuffer = pDestination;

    /* The first byte of a UTF-8 string is the high byte of the string length. */
    *pBuffer = UINT16_HIGH_BYTE( sourceLength );
    pBuffer++;

    /* The second byte of a UTF-8 string is the low byte of the string length. */
    *pBuffer = UINT16_LOW_BYTE( sourceLength );
    pBuffer++;

    /* Copy the string into pBuffer. */
    ( void ) memcpy( pBuffer, pSourceBuffer, sourceLength );

    /* Return the pointer to the end of the encoded string. */
    pBuffer += sourceLength;

    return ( size_t ) ( pBuffer - pDestination );
}

/**
 * @brief Check the serialization of an MQTT CONNECT packet in the given buffer,
 * following the same order in serializeConnectPacket.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[in] remainingLength Remaining Length of MQTT CONNECT packet.
 * @param[in] pBuffer Buffer to check packet serialization.
 *
 */
static void verifySerializedConnectPacket( const MQTTConnectInfo_t * const pConnectInfo,
                                           const MQTTPublishInfo_t * const pWillInfo,
                                           size_t remainingLength,
                                           const MQTTFixedBuffer_t * const pBuffer )
{
    uint8_t connectFlags = 0U;
    uint8_t encodedRemainingLength = 0U;
    uint8_t encodedStringLength = 0U;
    uint8_t * pIndex = NULL;

    pIndex = pBuffer->pBuffer;
    /* The first byte in the CONNECT packet is the control packet type. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_TYPE_CONNECT, *pIndex );
    pIndex++;

    /* The remaining length of the CONNECT packet is encoded starting from the
     * second byte. The remaining length does not include the length of the fixed
     * header or the encoding of the remaining length. */
    encodedRemainingLength = encodeRemainingLength( remainingLengthBuffer, remainingLength );
    TEST_ASSERT_EQUAL_MEMORY( remainingLengthBuffer, pIndex, encodedRemainingLength );
    pIndex += encodedRemainingLength;

    /* The string "MQTT" is placed at the beginning of the CONNECT packet's variable
     * header. This string is 4 bytes long. */
    encodedStringLength = encodeString( encodedStringBuffer, "MQTT", 4 );
    TEST_ASSERT_EQUAL_MEMORY( encodedStringBuffer, pIndex, encodedStringLength );
    pIndex += encodedStringLength;

    /* The MQTT protocol version is the second field of the variable header. */
    TEST_ASSERT_EQUAL( MQTT_VERSION_3_1_1, *pIndex );
    pIndex++;

    /* Set the clean session flag if needed. */
    if( pConnectInfo->cleanSession == true )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_CLEAN );
    }

    /* Set the flags for username and password if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_USERNAME );
    }

    if( pConnectInfo->pPassword != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_PASSWORD );
    }

    /* Set will flag if a Last Will and Testament is provided. */
    if( pWillInfo != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL );

        /* Flags only need to be changed for Will QoS 1 or 2. */
        if( pWillInfo->qos == MQTTQoS1 )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS1 );
        }
        else if( pWillInfo->qos == MQTTQoS2 )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS2 );
        }
        else
        {
            /* Empty else MISRA 15.7 */
        }

        if( pWillInfo->retain == true )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_RETAIN );
        }
    }

    TEST_ASSERT_EQUAL( connectFlags, *pIndex );
    pIndex++;

    /* Verify the 2 bytes of the keep alive interval into the CONNECT packet. */
    TEST_ASSERT_EQUAL( pConnectInfo->keepAliveSeconds,
                       UINT16_HIGH_BYTE( pConnectInfo->keepAliveSeconds ) );
    TEST_ASSERT_EQUAL( pConnectInfo->keepAliveSeconds,
                       UINT16_LOW_BYTE( pConnectInfo->keepAliveSeconds ) );
    pIndex += 2;

    /* Verify the client identifier into the CONNECT packet. */
    encodedStringLength = encodeString( encodedStringBuffer,
                                        pConnectInfo->pClientIdentifier,
                                        pConnectInfo->clientIdentifierLength );
    TEST_ASSERT_EQUAL_MEMORY( encodedStringBuffer, pIndex, encodedStringLength );
    pIndex += encodedStringLength;

    /* Verify the will topic name and message into the CONNECT packet if provided. */
    if( pWillInfo != NULL )
    {
        encodedStringLength = encodeString( encodedStringBuffer,
                                            pWillInfo->pTopicName,
                                            pWillInfo->topicNameLength );
        TEST_ASSERT_EQUAL_MEMORY( encodedStringBuffer, pIndex, encodedStringLength );
        pIndex += encodedStringLength;
        encodedStringLength = encodeString( encodedStringBuffer,
                                            pWillInfo->pPayload,
                                            ( uint16_t ) pWillInfo->payloadLength );
        TEST_ASSERT_EQUAL_MEMORY( encodedStringBuffer, pIndex, encodedStringLength );
        pIndex += encodedStringLength;
    }

    /* Verify the user name if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        encodedStringLength = encodeString( encodedStringBuffer,
                                            pConnectInfo->pUserName,
                                            pConnectInfo->userNameLength );
        TEST_ASSERT_EQUAL_MEMORY( encodedStringBuffer, pIndex, encodedStringLength );
        pIndex += encodedStringLength;
    }

    /* Verify the password if provided. */
    if( pConnectInfo->pPassword != NULL )
    {
        encodedStringLength = encodeString( encodedStringBuffer,
                                            pConnectInfo->pPassword,
                                            pConnectInfo->passwordLength );
        TEST_ASSERT_EQUAL_MEMORY( encodedStringBuffer, pIndex, encodedStringLength );
        pIndex += encodedStringLength;
    }
}

/**
 * @brief Call Mqtt_SerializeConnect using NULL parameters and insufficient buffer
 * size until we receive all possible MQTTBadParameter and MQTTNoMemory errors.
 */
void test_MQTT_SerializeConnect_invalid_params()
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t remainingLength = 0, packetSize = 0;
    MQTTFixedBuffer_t networkBuffer;
    MQTTConnectInfo_t connectInfo;

    /* Test NULL pConnectInfo. */
    mqttStatus = MQTT_SerializeConnect( NULL, NULL,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Test NULL pBuffer. */
    mqttStatus = MQTT_SerializeConnect( &connectInfo, NULL,
                                        remainingLength, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Test connectPacketSize > pBuffer->size. */
    /* Get MQTT connect packet size and remaining length. */
    mqttStatus = MQTT_GetConnectPacketSize( &connectInfo,
                                            NULL,
                                            &remainingLength,
                                            &packetSize );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    networkBuffer.pBuffer = mqttBuffer;
    networkBuffer.size = remainingLength - 1;
    mqttStatus = MQTT_SerializeConnect( &connectInfo, NULL,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTNoMemory, mqttStatus );
}

/**
 * @brief This method calls MQTT_SerializeConnect successfully using different parameters
 * until we have full coverage on the private method, serializeConnectPacket(...).
 */
void test_MQTT_SerializeConnect_happy_paths()
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t remainingLength = 0, packetSize = 0;
    MQTTFixedBuffer_t networkBuffer;
    MQTTConnectInfo_t connectInfo;
    MQTTPublishInfo_t willInfo;

    /* Fill structs to pass into methods to be tested. */
    setupNetworkBuffer( &networkBuffer );
    setupConnectInfo( &connectInfo );
    setupWillInfo( &willInfo );

    /* Get MQTT connect packet size and remaining length. */
    mqttStatus = MQTT_GetConnectPacketSize( &connectInfo,
                                            &willInfo,
                                            &remainingLength,
                                            &packetSize );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Make sure buffer has enough space. */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, networkBuffer.size );
    mqttStatus = MQTT_SerializeConnect( &connectInfo, &willInfo,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    verifySerializedConnectPacket( &connectInfo, &willInfo,
                                   remainingLength, &networkBuffer );

    /* Repeat with QoS2. */
    willInfo.qos = MQTTQoS2;
    mqttStatus = MQTT_GetConnectPacketSize( &connectInfo,
                                            &willInfo,
                                            &remainingLength,
                                            &packetSize );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Make sure buffer has enough space. */
    TEST_ASSERT_GREATER_OR_EQUAL( packetSize, networkBuffer.size );
    mqttStatus = MQTT_SerializeConnect( &connectInfo, &willInfo,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    verifySerializedConnectPacket( &connectInfo, &willInfo,
                                   remainingLength, &networkBuffer );
}

/* ========================================================================== */
