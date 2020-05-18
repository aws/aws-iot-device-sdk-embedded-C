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

/* ============================   Testing MQTT_Init ========================= */
void test_Mqtt_init_complete( void )
{
    MQTTContext_t context;
    MQTTTransportInterface_t transport;
    MQTTFixedBuffer_t networkBuffer;
    MQTTApplicationCallbacks_t callbacks;

    MQTT_Init( &context, &transport, &callbacks, &networkBuffer );
    TEST_ASSERT_EQUAL( context.connectStatus, MQTTNotConnected );
    /* These Unity assertions take pointers and compare their contents. */
    TEST_ASSERT_EQUAL_MEMORY( &context.transportInterface, &transport, sizeof( transport ) );
    TEST_ASSERT_EQUAL_MEMORY( &context.callbacks, &callbacks, sizeof( callbacks ) );
    TEST_ASSERT_EQUAL_MEMORY( &context.networkBuffer, &networkBuffer, sizeof( networkBuffer ) );
}
