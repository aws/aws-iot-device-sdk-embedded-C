#include <stdbool.h>

#include "unity.h"

#include "mock_mqtt_lightweight.h"

/* Include paths for public enums, structures, and macros. */
#include "mqtt.h"

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

/* ============================   Testing MQTT_Connect ====================== */
void test_Mqtt_connect_packet_size_gt_max( void )
{
    /* This mocked method will be called inside MQTT_Connect(...). */
    MQTT_GetConnectPacketSize_ExpectAnyArgsAndReturn( MQTTBadParameter );

    TEST_ASSERT_EQUAL( MQTT_Connect( NULL, NULL, NULL, NULL ), MQTTBadParameter );
}
