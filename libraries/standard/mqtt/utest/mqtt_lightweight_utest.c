#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "mqtt_lightweight.h"

/**
 * @brief Test-defined macro for MQTT username.
 */
#define MQTT_TEST_USERNAME         "username"
#define MQTT_TEST_USERNAME_LEN     sizeof( MQTT_TEST_USERNAME ) - 1

/**
 * @brief Test-defined macro for MQTT password.
 */
#define MQTT_TEST_PASSWORD         "password"
#define MQTT_TEST_PASSWORD_LEN     sizeof( MQTT_TEST_PASSWORD ) - 1

/**
 * @brief Test-defined macro for MQTT topic.
 */
#define MQTT_TEST_TOPIC            "topic"
#define MQTT_TEST_TOPIC_LEN        sizeof( MQTT_TEST_TOPIC ) - 1

/**
 * @brief Length of the client identifier.
 */
#define CLIENT_IDENTIFIER_LEN      sizeof( CLIENT_IDENTIFIER ) - 1

#define MQTT_TEST_BUFFER_LENGTH    ( 1024 )

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
 * @brief Successfully call Mqtt_SerializeConnect using different parameters
 * until we have full coverage on the private method, serializeConnectPacket(...).
 */
void test_Mqtt_SerializeConnect_invalid_params()
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t remainingLength, packetSize;
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
 * @brief This method calls Mqtt_SerializeConnect successfully using different parameters
 * until we have full coverage on the private method, serializeConnectPacket(...).
 */
void test_Mqtt_SerializeConnect_happy_path()
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t remainingLength, packetSize;
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
    mqttStatus = MQTT_SerializeConnect( &connectInfo, &willInfo,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Repeat with QoS2. */
    willInfo.qos = MQTTQoS2;
    mqttStatus = MQTT_GetConnectPacketSize( &connectInfo,
                                            &willInfo,
                                            &remainingLength,
                                            &packetSize );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    mqttStatus = MQTT_SerializeConnect( &connectInfo, &willInfo,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/* ========================================================================== */
