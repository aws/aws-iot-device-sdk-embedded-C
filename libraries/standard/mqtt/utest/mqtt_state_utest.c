#include "unity.h"

#include "mqtt_state.h"

#define MQTT_PACKET_ID_INVALID    ( uint16_t ) 0U

#define MQTT_STATE_ARRAY_MAX_COUNT 10U

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
    return numFailures;
}

/* ========================================================================== */

static void resetPublishRecords( MQTTContext_t * pMqttContext )
{
    int i = 0;
    for( ; i < MQTT_STATE_ARRAY_MAX_COUNT; i++ )
    {
        pMqttContext->outgoingPublishRecords[ i ].packetId = MQTT_PACKET_ID_INVALID;
        pMqttContext->outgoingPublishRecords[ i ].qos = MQTTQoS0;
        pMqttContext->outgoingPublishRecords[ i ].publishState = MQTTStateNull;
        pMqttContext->incomingPublishRecords[ i ].packetId = MQTT_PACKET_ID_INVALID;
        pMqttContext->incomingPublishRecords[ i ].qos = MQTTQoS0;
        pMqttContext->incomingPublishRecords[ i ].publishState = MQTTStateNull;
    }
}

static void addToRecord( MQTTPubAckInfo_t * records,
                         size_t index,
                         uint16_t packetId,
                         MQTTQoS_t qos,
                         MQTTPublishState_t state )
{
    records[ index ].packetId = packetId;
    records[ index ].qos = qos;
    records[ index ].publishState = state;
}

/* ========================================================================== */

void test_MQTT_ReserveState( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    int i;

    /* QoS 0 returns success. */
    TEST_ASSERT_EQUAL( MQTT_ReserveState( NULL, MQTT_PACKET_ID_INVALID, MQTTQoS0 ), MQTTSuccess );

    /* Test for bad parameters */
    status = MQTT_ReserveState( &mqttContext, MQTT_PACKET_ID_INVALID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( status, MQTTBadParameter );
    status = MQTT_ReserveState( NULL, 1, MQTTQoS1 );
    TEST_ASSERT_EQUAL( status, MQTTBadParameter );

    /* Test for collisions. */
    mqttContext.outgoingPublishRecords[ 1 ].packetId = 1;
    mqttContext.outgoingPublishRecords[ 1 ].qos = MQTTQoS1;
    mqttContext.outgoingPublishRecords[ 1 ].publishState = MQTTPublishSend;

    status = MQTT_ReserveState( &mqttContext, 1, MQTTQoS1 );
    TEST_ASSERT_EQUAL( status, MQTTStateCollision );

    /* Test for no memory. */
    for( i = 0; i < MQTT_STATE_ARRAY_MAX_COUNT; i++ )
    {
        mqttContext.outgoingPublishRecords[ i ].packetId = 2;
        mqttContext.outgoingPublishRecords[ i ].qos = MQTTQoS1;
        mqttContext.outgoingPublishRecords[ i ].publishState = MQTTPublishSend;
    }
    status = MQTT_ReserveState( &mqttContext, 1, MQTTQoS1 );
    TEST_ASSERT_EQUAL( status, MQTTNoMemory );

    /* Success. */
    resetPublishRecords( &mqttContext );
    status = MQTT_ReserveState( &mqttContext, 1, MQTTQoS1 );
    TEST_ASSERT_EQUAL( status, MQTTSuccess );
    /* Reserve uses first available entry. */
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].packetId, 1 );
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].qos, MQTTQoS1 );
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].publishState, MQTTPublishSend );
}

/* ========================================================================== */

void test_MQTT_CalculateStatePublish( void )
{
    /* QoS 0. */
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_SEND, MQTTQoS0 ), MQTTPublishDone );
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_RECEIVE, MQTTQoS0 ), MQTTPublishDone );

    /* QoS 1. */
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_SEND, MQTTQoS1 ), MQTTPubAckPending );
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_RECEIVE, MQTTQoS1 ), MQTTPubAckSend );

    /* QoS 2. */
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_SEND, MQTTQoS2 ), MQTTPubRecPending );
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_RECEIVE, MQTTQoS2 ), MQTTPubRecSend );

    /* Invalid QoS. */
    TEST_ASSERT_EQUAL( MQTT_CalculateStatePublish( MQTT_SEND, 3 ), MQTTStateNull );
}

/* ========================================================================== */

void test_MQTT_UpdateStatePublish( void )
{
    MQTTContext_t mqttContext = { 0 };
    const uint16_t PACKET_ID = 1;
    MQTTStateOperation_t operation = MQTT_SEND;
    MQTTQoS_t qos = MQTTQoS0;
    MQTTPublishState_t state;
    int i = 0;

    /* QoS 0. */
    state = MQTT_UpdateStatePublish( &mqttContext, 0, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTPublishDone );

    /* Invalid parameters. */
    /* Invalid ID. */
    qos = MQTTQoS1;
    state = MQTT_UpdateStatePublish( &mqttContext, 0, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    /* NULL context. */
    state = MQTT_UpdateStatePublish( NULL, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    /* No record found. */
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    /* QoS mismatch. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Invalid transition. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckPending );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Invalid QoS. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, 3, MQTTPublishSend );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, 3 );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    operation = MQTT_RECEIVE;
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, 3 );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Invalid current state. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, qos, MQTTStateNull );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Collision. */
    operation = MQTT_RECEIVE;
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckSend );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* No memory. */
    operation = MQTT_RECEIVE;
    for( i = 0; i < MQTT_STATE_ARRAY_MAX_COUNT; i++ )
    {
        mqttContext.incomingPublishRecords[ i ].packetId = 2;
        mqttContext.incomingPublishRecords[ i ].qos = MQTTQoS1;
        mqttContext.incomingPublishRecords[ i ].publishState = MQTTPublishSend;
    }
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    resetPublishRecords( &mqttContext );

    /* QoS 1. */
    qos = MQTTQoS1;
    /* Send. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPublishSend );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTPubAckPending );
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].publishState, MQTTPubAckPending );
    /* Receive. */
    operation = MQTT_RECEIVE;
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTPubAckSend );
    TEST_ASSERT_EQUAL( mqttContext.incomingPublishRecords[ 0 ].publishState, MQTTPubAckSend );

    resetPublishRecords( &mqttContext );

    /* QoS 2. */
    qos = MQTTQoS2;
    /* Send. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTPubRecPending );
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].publishState, MQTTPubRecPending );
    /* Receive. */
    operation = MQTT_RECEIVE;
    state = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos );
    TEST_ASSERT_EQUAL( state, MQTTPubRecSend );
    TEST_ASSERT_EQUAL( mqttContext.incomingPublishRecords[ 0 ].publishState, MQTTPubRecSend );

}

/* ========================================================================== */

void test_MQTT_CalculateStateAck( void )
{
    MQTTPubAckType_t ack;
    MQTTQoS_t qos;
    MQTTStateOperation_t opType;

    /* Invalid qos. */
    qos = MQTTQoS0;
    ack = MQTTPuback;
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTStateNull );
    qos = MQTTQoS2;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTStateNull );
    qos = MQTTQoS0;
    ack = MQTTPubrec;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTStateNull );
    qos = MQTTQoS1;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTStateNull );

    /* Invalid ack type. */
    ack = MQTTPubcomp + 1;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTStateNull );

    /* PUBACK */
    ack = MQTTPuback;
    qos = MQTTQoS1;
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPublishDone );
    opType = MQTT_RECEIVE;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPublishDone );

    /* QoS 2 tests. */
    qos = MQTTQoS2;

    /* PUBREC */
    ack = MQTTPubrec;
    /* Send */
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPubRelPending );
    /* Receive */
    opType = MQTT_RECEIVE;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPubRelSend );

    /* PUBREL */
    ack = MQTTPubrel;
    /* Send */
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPubCompPending );
    /* Receive */
    opType = MQTT_RECEIVE;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPubCompSend );

    /* PUBCOMP */
    ack = MQTTPubcomp;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPublishDone );
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTT_CalculateStateAck( ack, opType, qos ), MQTTPublishDone );
}

/* ========================================================================== */

void test_MQTT_UpdateStateAck( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPubAckType_t ack = MQTTPuback;
    MQTTStateOperation_t operation = MQTT_RECEIVE;
    MQTTPublishState_t state = MQTTStateNull;

    const uint16_t PACKET_ID = 1;

    /* No matching record found. */
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    /* Invalid packet ID. */
    state = MQTT_UpdateStateAck( &mqttContext, 0, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Invalid transition. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    ack = MQTTPubcomp;
    state = MQTT_UpdateStateAck( &mqttContext, 1, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Invalid ack type. */
    state = MQTT_UpdateStateAck( &mqttContext, 1, MQTTPubcomp + 1, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    /* Invalid current state. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishDone );
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTStateNull );
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTStateNull );

    resetPublishRecords( &mqttContext );

    /* QoS 1, outgoing publish. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckPending );
    operation = MQTT_RECEIVE;
    ack = MQTTPuback;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPublishDone );
    /* Test for deletion. */
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].publishState, MQTTStateNull );
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].packetId, MQTT_PACKET_ID_INVALID );
    TEST_ASSERT_EQUAL( mqttContext.outgoingPublishRecords[ 0 ].qos, MQTTQoS0 );
    /* Incoming publish. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckSend );
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPublishDone );

    resetPublishRecords( &mqttContext );

    /* QoS 2, PUBREL. */
    /* Outgoing. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelSend );
    operation = MQTT_SEND;
    ack = MQTTPubrel;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPubCompPending );
    /* Incoming . */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelPending );
    operation = MQTT_RECEIVE;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPubCompSend );
    /* Test for update. */
    TEST_ASSERT_EQUAL( mqttContext.incomingPublishRecords[ 0 ].publishState, MQTTPubCompSend );

    /* QoS 2, PUBREC. */
    /* Outgoing. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    operation = MQTT_RECEIVE;
    ack = MQTTPubrec;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPubRelSend );
    /* Incoming. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecSend );
    operation = MQTT_SEND;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPubRelPending );

    /* QoS 2, PUBCOMP. */
    /* Outgoing. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubCompPending );
    operation = MQTT_RECEIVE;
    ack = MQTTPubcomp;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPublishDone );
    /* Incoming. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubCompSend );
    operation = MQTT_SEND;
    state = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation );
    TEST_ASSERT_EQUAL( state, MQTTPublishDone );
}

/* ========================================================================== */

void test_MQTT_StateSelect( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStateCursor_t outgoingCursor = MQTT_STATE_CURSOR_INITIALIZER;
    MQTTStateCursor_t incomingCursor = MQTT_STATE_CURSOR_INITIALIZER;
    MQTTPublishState_t search = MQTTPublishSend;
    uint16_t packetId;
    const uint16_t PACKET_ID = 1;
    const uint16_t PACKET_ID2 = 2;
    const size_t index = MQTT_STATE_ARRAY_MAX_COUNT / 2;
    const size_t secondIndex = index + 2;

    /* Invalid parameters. */
    packetId = MQTT_StateSelect( NULL, MQTTPublishSend, &outgoingCursor );
    TEST_ASSERT_EQUAL( packetId, MQTT_PACKET_ID_INVALID );
    packetId = MQTT_StateSelect( NULL, MQTTPubAckSend, &incomingCursor );
    TEST_ASSERT_EQUAL( packetId, MQTT_PACKET_ID_INVALID );
    packetId = MQTT_StateSelect( &mqttContext, search, NULL );
    TEST_ASSERT_EQUAL( packetId, MQTT_PACKET_ID_INVALID );
    packetId = MQTT_StateSelect( &mqttContext, MQTTStateNull, &outgoingCursor );
    TEST_ASSERT_EQUAL( packetId, MQTT_PACKET_ID_INVALID );

    /* Incoming. */
    search = MQTTPubAckSend;
    addToRecord( mqttContext.incomingPublishRecords, index, PACKET_ID, MQTTQoS1, search );
    packetId = MQTT_StateSelect( &mqttContext, search, &incomingCursor );
    TEST_ASSERT_EQUAL( packetId, PACKET_ID );
    TEST_ASSERT_EQUAL( incomingCursor, index + 1 );

    /* Outgoing. */
    search = MQTTPublishSend;
    addToRecord( mqttContext.outgoingPublishRecords, index, PACKET_ID, MQTTQoS1, search );
    packetId = MQTT_StateSelect( &mqttContext, search, &outgoingCursor );
    TEST_ASSERT_EQUAL( packetId, PACKET_ID );
    TEST_ASSERT_EQUAL( outgoingCursor, index + 1 );

    /* Test if second one can be found. */
    addToRecord( mqttContext.outgoingPublishRecords, secondIndex, PACKET_ID2, MQTTQoS2, search );
    packetId = MQTT_StateSelect( &mqttContext, search, &outgoingCursor );
    TEST_ASSERT_EQUAL( packetId, PACKET_ID2 );
    TEST_ASSERT_EQUAL( outgoingCursor, secondIndex + 1 );

    /* Test if end of loop reached. */
    packetId = MQTT_StateSelect( &mqttContext, search, &outgoingCursor );
    TEST_ASSERT_EQUAL( packetId, MQTT_PACKET_ID_INVALID );
    TEST_ASSERT_EQUAL( outgoingCursor, MQTT_STATE_ARRAY_MAX_COUNT );
}
