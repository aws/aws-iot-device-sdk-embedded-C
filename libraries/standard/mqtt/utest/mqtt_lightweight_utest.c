#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "mqtt.h"
#include "mqtt_lightweight.h"

/**
 * @brief Size of the fixed and variable header of a CONNECT packet.
 */
#define MQTT_PACKET_CONNECT_HEADER_SIZE    ( 10UL )

/**
 * @brief Test-defined macros for MQTT.
 */
#define MQTT_TEST_USERNAME                 "username"
#define MQTT_TEST_USERNAME_LEN             sizeof( MQTT_TEST_USERNAME ) - 1

#define MQTT_TEST_PASSWORD                 "password"
#define MQTT_TEST_PASSWORD_LEN             sizeof( MQTT_TEST_PASSWORD ) - 1

#define MQTT_TEST_TOPIC                    "topic"
#define MQTT_TEST_TOPIC_LEN                sizeof( MQTT_TEST_TOPIC ) - 1

#define CLIENT_IDENTIFIER_LEN              sizeof( CLIENT_IDENTIFIER ) - 1

#define MQTT_TEST_BUFFER_LENGTH            ( 1024 )

static uint8_t mqttBuffer[ MQTT_TEST_BUFFER_LENGTH ] = { 0 };

/* ============================   UNITY FIXTURES ============================ */
void setUp( void )
{
}

/* called before each testcase */
void tearDown( void )
{
}

/* called at the beginning of the whole suite */
void suiteSetUp()
{
}

/* called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
}

/* =====================  Testing MQTT_SerializeConnect ===================== */

void test_Mqtt_SerializeConnect_invalid_params()
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t remainingLength, packetSize;
    MQTTFixedBuffer_t networkBuffer;
    MQTTConnectInfo_t connectInfo;

    /* Test NULL pConnectInfo. */
    mqttStatus = MQTT_SerializeConnect( NULL, NULL, remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTBadParameter );

    /* Test NULL pBuffer. */
    mqttStatus = MQTT_SerializeConnect( &connectInfo, NULL, remainingLength, NULL );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTBadParameter );

    /* Test connectPacketSize > pBuffer->size. */
    networkBuffer.pBuffer = mqttBuffer;
    networkBuffer.size = MQTT_PACKET_CONNECT_HEADER_SIZE - 1;
    mqttStatus = MQTT_SerializeConnect( &connectInfo, NULL,
                                        remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTNoMemory );
}

void test_Mqtt_SerializeConnect_happy_path()
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t remainingLength, packetSize;
    MQTTFixedBuffer_t networkBuffer;
    MQTTConnectInfo_t connectInfo;
    MQTTPublishInfo_t willInfo;

    networkBuffer.pBuffer = mqttBuffer;
    networkBuffer.size = MQTT_TEST_BUFFER_LENGTH;

    connectInfo.cleanSession = true;
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LEN;
    connectInfo.keepAliveSeconds = 0;
    connectInfo.pUserName = MQTT_TEST_USERNAME;
    connectInfo.userNameLength = MQTT_TEST_USERNAME_LEN;
    connectInfo.pPassword = MQTT_TEST_PASSWORD;
    connectInfo.passwordLength = MQTT_TEST_PASSWORD_LEN;

    willInfo.pPayload = NULL;
    willInfo.payloadLength = 0;
    willInfo.pTopicName = CLIENT_IDENTIFIER;
    willInfo.topicNameLength = CLIENT_IDENTIFIER_LEN;
    willInfo.dup = true;
    willInfo.qos = MQTTQoS1;
    willInfo.retain = true;

    /* We successfully call Mqtt_SerializeConnect until we have full coverage
     * on the private method, serializeConnectPacket(...). */

    /* Get MQTT connect packet size and remaining length. */
    mqttStatus = MQTT_GetConnectPacketSize( &connectInfo,
                                            &willInfo,
                                            &remainingLength,
                                            &packetSize );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTSuccess );
    mqttStatus = MQTT_SerializeConnect( &connectInfo, &willInfo, remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTSuccess );

    /* Repeat with QoS2. */
    willInfo.qos = MQTTQoS2;
    mqttStatus = MQTT_GetConnectPacketSize( &connectInfo,
                                            &willInfo,
                                            &remainingLength,
                                            &packetSize );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTSuccess );
    mqttStatus = MQTT_SerializeConnect( &connectInfo, &willInfo, remainingLength, &networkBuffer );
    TEST_ASSERT_EQUAL( mqttStatus, MQTTSuccess );
}

/* ========================================================================== */
