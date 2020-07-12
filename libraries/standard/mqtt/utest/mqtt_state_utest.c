#include <string.h>
#include "unity.h"

#include "mqtt_state.h"

#define MQTT_PACKET_ID_INVALID    ( ( uint16_t ) 0U )

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

static void fillRecord( MQTTPubAckInfo_t * records,
                        uint16_t startingId,
                        MQTTQoS_t qos,
                        MQTTPublishState_t state )
{
    int i;

    for( i = 0; i < MQTT_STATE_ARRAY_MAX_COUNT; i++ )
    {
        records[ i ].packetId = startingId + i;
        records[ i ].qos = qos;
        records[ i ].publishState = state;
    }
}

static void validateRecordAt( MQTTPubAckInfo_t * records,
                              size_t index,
                              uint16_t packetId,
                              MQTTQoS_t qos,
                              MQTTPublishState_t state )
{
    TEST_ASSERT_EQUAL( packetId, records[ index ].packetId );
    TEST_ASSERT_EQUAL( qos, records[ index ].qos );
    TEST_ASSERT_EQUAL( state, records[ index ].publishState );
}

/* ========================================================================== */

void test_MQTT_ReserveState( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    const uint16_t PACKET_ID = 1;
    const uint16_t PACKET_ID2 = 2;
    const uint16_t PACKET_ID3 = 3;
    const size_t index = MQTT_STATE_ARRAY_MAX_COUNT / 2;

    /* QoS 0 returns success. */
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_ReserveState( NULL, MQTT_PACKET_ID_INVALID, MQTTQoS0 ) );

    /* Test for bad parameters */
    status = MQTT_ReserveState( &mqttContext, MQTT_PACKET_ID_INVALID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    status = MQTT_ReserveState( NULL, PACKET_ID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );

    /* Test for collisions. */
    mqttContext.outgoingPublishRecords[ 1 ].packetId = PACKET_ID;
    mqttContext.outgoingPublishRecords[ 1 ].qos = MQTTQoS1;
    mqttContext.outgoingPublishRecords[ 1 ].publishState = MQTTPublishSend;

    status = MQTT_ReserveState( &mqttContext, PACKET_ID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTStateCollision, status );

    /* Test for no memory. */
    fillRecord( mqttContext.outgoingPublishRecords, 2, MQTTQoS1, MQTTPublishSend );
    status = MQTT_ReserveState( &mqttContext, PACKET_ID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTNoMemory, status );

    /* Success. */
    resetPublishRecords( &mqttContext );
    status = MQTT_ReserveState( &mqttContext, PACKET_ID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    /* Reserve uses first available entry. */
    TEST_ASSERT_EQUAL( PACKET_ID, mqttContext.outgoingPublishRecords[ 0 ].packetId );
    TEST_ASSERT_EQUAL( MQTTQoS1, mqttContext.outgoingPublishRecords[ 0 ].qos );
    TEST_ASSERT_EQUAL( MQTTPublishSend, mqttContext.outgoingPublishRecords[ 0 ].publishState );

    /* Success.
     * Add record after the highest non empty index.
     * Already an entry exists at index 0. Adding 1 more entry at index 5.
     * The new index used should be 6. */
    addToRecord( mqttContext.outgoingPublishRecords, index, PACKET_ID2, MQTTQoS2, MQTTPubRelSend );
    status = MQTT_ReserveState( &mqttContext, PACKET_ID3, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( PACKET_ID3, mqttContext.outgoingPublishRecords[ index + 1 ].packetId );
    TEST_ASSERT_EQUAL( MQTTQoS1, mqttContext.outgoingPublishRecords[ index + 1 ].qos );
    TEST_ASSERT_EQUAL( MQTTPublishSend, mqttContext.outgoingPublishRecords[ index + 1 ].publishState );
}

/* ========================================================================== */

void test_MQTT_ReserveState_compactRecords( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStatus_t status;
    const uint16_t PACKET_ID = 1;
    const uint16_t PACKET_ID2 = 2;

    /* Consider the state of the array with 2 states. 1 indicates a non empty
     * spot and 0 an empty spot. Size of the array is 10.
     * Pre condition - 0 0 0 0 0 0 0 0 0 1.
     * Add an element will try to compact the array and the resulting state
     * should be - 1 1 0 0 0 0 0 0 0 0. */
    addToRecord( mqttContext.outgoingPublishRecords, MQTT_STATE_ARRAY_MAX_COUNT - 1, PACKET_ID, MQTTQoS1, MQTTPubRelSend );
    status = MQTT_ReserveState( &mqttContext, PACKET_ID2, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    /* The existing record should be at index 0. */
    validateRecordAt( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubRelSend );
    /* New record should be added to index 1. */
    validateRecordAt( mqttContext.outgoingPublishRecords, 1, PACKET_ID2, MQTTQoS1, MQTTPublishSend );

    /* One free spot.
     * Pre condition - 1 1 1 0 1 1 1 1 1 1.
     * Add an element will try to compact the array and the resulting state
     * should be - 1 1 1 1 1 1 1 1 1 1. */
    fillRecord( mqttContext.outgoingPublishRecords, PACKET_ID2 + 1, MQTTQoS2, MQTTPubRelSend );
    /* Invalid record at index 3. */
    mqttContext.outgoingPublishRecords[ 3 ].packetId = MQTT_PACKET_ID_INVALID;
    status = MQTT_ReserveState( &mqttContext, PACKET_ID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    /* The new record should be added to the end. */
    validateRecordAt( mqttContext.outgoingPublishRecords,
                      MQTT_STATE_ARRAY_MAX_COUNT - 1,
                      PACKET_ID,
                      MQTTQoS1,
                      MQTTPublishSend );
    /* Any new add should result in no memory error. */
    status = MQTT_ReserveState( &mqttContext, PACKET_ID2, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTNoMemory, status );

    /* Alternate free spots.
     * Pre condition - 1 0 1 0 1 0 1 0 1 0.
     * Add an element will skip to compact the array and the resulting state
     * should be - 1 0 1 0 1 0 1 0 1 1. */
    fillRecord( mqttContext.outgoingPublishRecords, PACKET_ID2 + 1, MQTTQoS2, MQTTPubRelSend );
    /* Invalidate record at alternate indexes starting from 1. */
    mqttContext.outgoingPublishRecords[ 1 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 3 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 5 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 7 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 9 ].packetId = MQTT_PACKET_ID_INVALID;
    status = MQTT_ReserveState( &mqttContext, PACKET_ID, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    /* The new record should be added to the end. */
    validateRecordAt( mqttContext.outgoingPublishRecords,
                      MQTT_STATE_ARRAY_MAX_COUNT - 1,
                      PACKET_ID,
                      MQTTQoS1,
                      MQTTPublishSend );

    /* Array is in state 1 0 1 0 1 0 1 0 1 1.
     * Adding one more element should result in array in state
     * 1 1 1 1 1 1 1 0 0 0. */
    status = MQTT_ReserveState( &mqttContext, PACKET_ID2, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    validateRecordAt( mqttContext.outgoingPublishRecords, 6, PACKET_ID2, MQTTQoS1, MQTTPublishSend );
    /* Remaining records should be invalid. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 7 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 8 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 9 ].packetId );

    /* Free spots only in the beginning.
     * Pre condition - 0 0 0 0 0 1 1 1 1 1.
     * Add an element will compact the array and the resulting state
     * should be - 1 1 1 1 1 1 0 0 0 0. */
    fillRecord( mqttContext.outgoingPublishRecords, PACKET_ID2 + 1, MQTTQoS2, MQTTPubRelSend );
    /* Clear record from 0 to 4. */
    ( void ) memset( &mqttContext.outgoingPublishRecords[ 0 ], 0x00, 5 * sizeof( MQTTPubAckInfo_t ) );

    /* Adding one element should result in array in state
     * 1 1 1 1 1 1 0 0 0 0. */
    status = MQTT_ReserveState( &mqttContext, PACKET_ID2, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    validateRecordAt( mqttContext.outgoingPublishRecords, 5, PACKET_ID2, MQTTQoS1, MQTTPublishSend );
    /* Remaining records should be cleared. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 6 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 7 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 8 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 9 ].packetId );

    /* Fragmented array.
     * Pre condition - 1 0 0 1 1 1 1 0 0 1.
     * Add an element will compact the array and the resulting state
     * should be - 1 1 1 1 1 1 1 0 0 0. */
    fillRecord( mqttContext.outgoingPublishRecords, PACKET_ID2 + 1, MQTTQoS2, MQTTPubRelSend );
    /* Clear record at index 1,2,7 and 8. */
    mqttContext.outgoingPublishRecords[ 1 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 2 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 7 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttContext.outgoingPublishRecords[ 8 ].packetId = MQTT_PACKET_ID_INVALID;
    status = MQTT_ReserveState( &mqttContext, PACKET_ID2, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    validateRecordAt( mqttContext.outgoingPublishRecords, 6, PACKET_ID2, MQTTQoS1, MQTTPublishSend );
    /* Remaining records should be cleared. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 7 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 8 ].packetId );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 9 ].packetId );

    /* Fragmented array.
     * Pre condition - 1 0 0 0 0 0 0 0 0 1.
     * Add an element will compact the array and the resulting state
     * should be - 1 1 1 0 0 0 0 0 0 0. */
    resetPublishRecords( &mqttContext );
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    addToRecord( mqttContext.outgoingPublishRecords, 9, PACKET_ID2 + 1, MQTTQoS2, MQTTPubCompPending );
    status = MQTT_ReserveState( &mqttContext, PACKET_ID2, MQTTQoS1 );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    validateRecordAt( mqttContext.outgoingPublishRecords, 2, PACKET_ID2, MQTTQoS1, MQTTPublishSend );
    /* Validate existing records. */
    validateRecordAt( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    validateRecordAt( mqttContext.outgoingPublishRecords, 1, PACKET_ID2 + 1, MQTTQoS2, MQTTPubCompPending );
}

/* ========================================================================== */

void test_MQTT_CalculateStatePublish( void )
{
    /* QoS 0. */
    TEST_ASSERT_EQUAL( MQTTPublishDone, MQTT_CalculateStatePublish( MQTT_SEND, MQTTQoS0 ) );
    TEST_ASSERT_EQUAL( MQTTPublishDone, MQTT_CalculateStatePublish( MQTT_RECEIVE, MQTTQoS0 ) );

    /* QoS 1. */
    TEST_ASSERT_EQUAL( MQTTPubAckPending, MQTT_CalculateStatePublish( MQTT_SEND, MQTTQoS1 ) );
    TEST_ASSERT_EQUAL( MQTTPubAckSend, MQTT_CalculateStatePublish( MQTT_RECEIVE, MQTTQoS1 ) );

    /* QoS 2. */
    TEST_ASSERT_EQUAL( MQTTPubRecPending, MQTT_CalculateStatePublish( MQTT_SEND, MQTTQoS2 ) );
    TEST_ASSERT_EQUAL( MQTTPubRecSend, MQTT_CalculateStatePublish( MQTT_RECEIVE, MQTTQoS2 ) );

    /* Invalid QoS. */
    TEST_ASSERT_EQUAL( MQTTStateNull, MQTT_CalculateStatePublish( MQTT_SEND, 3 ) );
}

/* ========================================================================== */

void test_MQTT_UpdateStatePublish( void )
{
    MQTTContext_t mqttContext = { 0 };
    const uint16_t PACKET_ID = 1;
    MQTTStateOperation_t operation = MQTT_SEND;
    MQTTQoS_t qos = MQTTQoS0;
    MQTTPublishState_t state;
    MQTTStatus_t status;

    /* QoS 0. */
    status = MQTT_UpdateStatePublish( &mqttContext, 0, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTPublishDone, state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );

    /* Invalid parameters. */
    /* Invalid ID. */
    qos = MQTTQoS1;
    status = MQTT_UpdateStatePublish( &mqttContext, 0, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    /* NULL context. */
    status = MQTT_UpdateStatePublish( NULL, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    /* NULL new state. */
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    /* No record found. */
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    /* QoS mismatch. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );

    /* Invalid state transition. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubRelPending );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );

    /* Invalid QoS. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, 3, MQTTPublishSend );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, 3, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );
    operation = MQTT_RECEIVE;
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, 3, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );

    /* Invalid current state. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, qos, MQTTStateNull );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );

    /* Collision. */
    operation = MQTT_RECEIVE;
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckSend );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTStateCollision, status );

    /* No memory. */
    operation = MQTT_RECEIVE;
    fillRecord( mqttContext.incomingPublishRecords, 2, MQTTQoS1, MQTTPublishSend );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTNoMemory, status );

    resetPublishRecords( &mqttContext );

    /* QoS 1. */
    qos = MQTTQoS1;
    /* Send. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPublishSend );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubAckPending, state );
    TEST_ASSERT_EQUAL( MQTTPubAckPending, mqttContext.outgoingPublishRecords[ 0 ].publishState );
    /* Resend when record already exists. */
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubAckPending, state );
    TEST_ASSERT_EQUAL( MQTTPubAckPending, mqttContext.outgoingPublishRecords[ 0 ].publishState );
    /* Receive. */
    operation = MQTT_RECEIVE;
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubAckSend, state );
    TEST_ASSERT_EQUAL( MQTTPubAckSend, mqttContext.incomingPublishRecords[ 0 ].publishState );
    /* Receive duplicate incoming publish. */
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTStateCollision, status );
    TEST_ASSERT_EQUAL( MQTTPubAckSend, state );
    TEST_ASSERT_EQUAL( MQTTPubAckSend, mqttContext.incomingPublishRecords[ 0 ].publishState );

    resetPublishRecords( &mqttContext );

    /* QoS 2. */
    qos = MQTTQoS2;
    /* Send. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRecPending, state );
    TEST_ASSERT_EQUAL( MQTTPubRecPending, mqttContext.outgoingPublishRecords[ 0 ].publishState );
    /* Resend when record already exists. */
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRecPending, state );
    TEST_ASSERT_EQUAL( MQTTPubRecPending, mqttContext.outgoingPublishRecords[ 0 ].publishState );
    /* Receive. */
    operation = MQTT_RECEIVE;
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRecSend, state );
    TEST_ASSERT_EQUAL( MQTTPubRecSend, mqttContext.incomingPublishRecords[ 0 ].publishState );
    /* Receive incoming publish when the packet record is in state #MQTTPubRecSend. */
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTStateCollision, status );
    TEST_ASSERT_EQUAL( MQTTPubRecSend, state );
    TEST_ASSERT_EQUAL( MQTTPubRecSend, mqttContext.incomingPublishRecords[ 0 ].publishState );
    /* Receive incoming publish when the packet record is in state #MQTTPubRelPending. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelPending );
    status = MQTT_UpdateStatePublish( &mqttContext, PACKET_ID, operation, qos, &state );
    TEST_ASSERT_EQUAL( MQTTStateCollision, status );
    /* The returned state will always be #MQTTPubRecSend as a PUBREC need to be sent. */
    TEST_ASSERT_EQUAL( MQTTPubRecSend, state );
    TEST_ASSERT_EQUAL( MQTTPubRelPending, mqttContext.incomingPublishRecords[ 0 ].publishState );
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
    TEST_ASSERT_EQUAL( MQTTStateNull, MQTT_CalculateStateAck( ack, opType, qos ) );
    qos = MQTTQoS2;
    TEST_ASSERT_EQUAL( MQTTStateNull, MQTT_CalculateStateAck( ack, opType, qos ) );
    qos = MQTTQoS0;
    ack = MQTTPubrec;
    TEST_ASSERT_EQUAL( MQTTStateNull, MQTT_CalculateStateAck( ack, opType, qos ) );
    qos = MQTTQoS1;
    TEST_ASSERT_EQUAL( MQTTStateNull, MQTT_CalculateStateAck( ack, opType, qos ) );

    /* Invalid ack type. */
    ack = MQTTPubcomp + 1;
    TEST_ASSERT_EQUAL( MQTTStateNull, MQTT_CalculateStateAck( ack, opType, qos ) );

    /* PUBACK */
    ack = MQTTPuback;
    qos = MQTTQoS1;
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTTPublishDone, MQTT_CalculateStateAck( ack, opType, qos ) );
    opType = MQTT_RECEIVE;
    TEST_ASSERT_EQUAL( MQTTPublishDone, MQTT_CalculateStateAck( ack, opType, qos ) );

    /* QoS 2 tests. */
    qos = MQTTQoS2;

    /* PUBREC */
    ack = MQTTPubrec;
    /* Send */
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTTPubRelPending, MQTT_CalculateStateAck( ack, opType, qos ) );
    /* Receive */
    opType = MQTT_RECEIVE;
    TEST_ASSERT_EQUAL( MQTTPubRelSend, MQTT_CalculateStateAck( ack, opType, qos ) );

    /* PUBREL */
    ack = MQTTPubrel;
    /* Send */
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTTPubCompPending, MQTT_CalculateStateAck( ack, opType, qos ) );
    /* Receive */
    opType = MQTT_RECEIVE;
    TEST_ASSERT_EQUAL( MQTTPubCompSend, MQTT_CalculateStateAck( ack, opType, qos ) );

    /* PUBCOMP */
    ack = MQTTPubcomp;
    TEST_ASSERT_EQUAL( MQTTPublishDone, MQTT_CalculateStateAck( ack, opType, qos ) );
    opType = MQTT_SEND;
    TEST_ASSERT_EQUAL( MQTTPublishDone, MQTT_CalculateStateAck( ack, opType, qos ) );
}

/* ========================================================================== */

void test_MQTT_UpdateStateAck( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTPubAckType_t ack = MQTTPuback;
    MQTTStateOperation_t operation = MQTT_RECEIVE;
    MQTTPublishState_t state = MQTTStateNull;
    MQTTStatus_t status;

    const uint16_t PACKET_ID = 1;

    /* NULL parameters. */
    status = MQTT_UpdateStateAck( NULL, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    /* No matching record found. */
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );
    /* Invalid packet ID. */
    status = MQTT_UpdateStateAck( &mqttContext, 0, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );

    /* Invalid transitions. */
    /* Invalid transition from #MQTTPubRelPending. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelPending );
    ack = MQTTPubrel;
    operation = MQTT_SEND;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );
    /* Invalid transition from #MQTTPubCompSend. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubCompSend );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );
    /* Invalid transition from #MQTTPubCompPending. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubCompPending );
    ack = MQTTPubrec;
    operation = MQTT_RECEIVE;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );
    /* Invalid transition from #MQTTPubRecPending. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    ack = MQTTPubcomp;
    status = MQTT_UpdateStateAck( &mqttContext, 1, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );

    /* Invalid ack type. */
    status = MQTT_UpdateStateAck( &mqttContext, 1, MQTTPubcomp + 1, operation, &state );
    TEST_ASSERT_EQUAL( MQTTBadParameter, status );

    /* Invalid current state. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishDone );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTStateNull );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTIllegalState, status );

    resetPublishRecords( &mqttContext );

    /* QoS 1, receive PUBACK for outgoing publish. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckPending );
    operation = MQTT_RECEIVE;
    ack = MQTTPuback;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPublishDone, state );

    /* Test for deletion. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 0 ].packetId );
    /* Send PUBACK for incoming publish. */
    operation = MQTT_SEND;
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS1, MQTTPubAckSend );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPublishDone, state );

    resetPublishRecords( &mqttContext );

    /* QoS 2, PUBREL. */
    /* Outgoing. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelSend );
    operation = MQTT_SEND;
    ack = MQTTPubrel;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubCompPending, state );
    /* Outgoing. Resend PUBREL when record in state #MQTTPubCompPending. */
    operation = MQTT_SEND;
    ack = MQTTPubrel;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubCompPending, state );
    /* Incoming. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelPending );
    operation = MQTT_RECEIVE;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubCompSend, state );
    /* Test for update. */
    TEST_ASSERT_EQUAL( MQTTPubCompSend, mqttContext.incomingPublishRecords[ 0 ].publishState );
    /* Incoming. Duplicate PUBREL is received when record is in state #MQTTPubRelPending. */
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubCompSend, state );

    /* QoS 2, PUBREC. */
    /* Outgoing. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    operation = MQTT_RECEIVE;
    ack = MQTTPubrec;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, state );

    /* Receiving a PUBREC will move the record to the end.
     * In this case, only one record exists, no moving is required. */
    TEST_ASSERT_EQUAL( PACKET_ID, mqttContext.outgoingPublishRecords[ 0 ].packetId );
    TEST_ASSERT_EQUAL( MQTTQoS2, mqttContext.outgoingPublishRecords[ 0 ].qos );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, mqttContext.outgoingPublishRecords[ 0 ].publishState );

    /* Outgoing.
     * Test if the record moves to the end of the records when PUBREC is
     * received. */
    resetPublishRecords( &mqttContext );
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecPending );
    addToRecord( mqttContext.outgoingPublishRecords, 1, PACKET_ID + 1, MQTTQoS2, MQTTPubRelSend );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, state );

    /* Receiving a PUBREC will move the record to the end.
    * In this case, the record wil be moved to index 2. */
    TEST_ASSERT_EQUAL( PACKET_ID, mqttContext.outgoingPublishRecords[ 2 ].packetId );
    TEST_ASSERT_EQUAL( MQTTQoS2, mqttContext.outgoingPublishRecords[ 2 ].qos );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, mqttContext.outgoingPublishRecords[ 2 ].publishState );
    /* Record at the current index will be marked as invalid. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttContext.outgoingPublishRecords[ 0 ].packetId );

    /* Incoming. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRecSend );
    operation = MQTT_SEND;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRelPending, state );
    /* Incoming. Duplicate publish received and record is in state #MQTTPubRelPending. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubRelPending );
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPubRelPending, state );

    /* QoS 2, PUBCOMP. */
    /* Outgoing. */
    addToRecord( mqttContext.outgoingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubCompPending );
    operation = MQTT_RECEIVE;
    ack = MQTTPubcomp;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPublishDone, state );
    /* Incoming. */
    addToRecord( mqttContext.incomingPublishRecords, 0, PACKET_ID, MQTTQoS2, MQTTPubCompSend );
    operation = MQTT_SEND;
    status = MQTT_UpdateStateAck( &mqttContext, PACKET_ID, ack, operation, &state );
    TEST_ASSERT_EQUAL( MQTTSuccess, status );
    TEST_ASSERT_EQUAL( MQTTPublishDone, state );
}

/* ========================================================================== */

void test_MQTT_AckToResend( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    MQTTPublishState_t state = MQTTStateNull;
    uint16_t packetId;
    const uint16_t PACKET_ID = 1;
    const uint16_t PACKET_ID2 = 2;
    const uint16_t PACKET_ID3 = 3;
    const uint16_t PACKET_ID4 = 4;
    const size_t index = 0;
    const size_t index2 = 1;
    const size_t index3 = MQTT_STATE_ARRAY_MAX_COUNT / 2;
    const size_t index4 = index3 + 2;

    /* Invalid parameters. */
    packetId = MQTT_PubrelToResend( NULL, &cursor, &state );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    packetId = MQTT_PubrelToResend( &mqttContext, NULL, &state );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, NULL );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );

    /* No packet exists. */
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    TEST_ASSERT_EQUAL( MQTTStateNull, state );
    TEST_ASSERT_EQUAL( MQTT_STATE_ARRAY_MAX_COUNT, cursor );

    /* No packet exists in state #MQTTPubCompPending or #MQTTPubCompPending states. */
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    addToRecord( mqttContext.outgoingPublishRecords, index, PACKET_ID3, MQTTQoS2, MQTTPubRelPending );
    addToRecord( mqttContext.outgoingPublishRecords, index2, PACKET_ID4, MQTTQoS2, MQTTPubCompSend );
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    TEST_ASSERT_EQUAL( MQTTStateNull, state );
    TEST_ASSERT_EQUAL( MQTT_STATE_ARRAY_MAX_COUNT, cursor );

    /* Add a record in #MQTTPubCompPending state. */
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    addToRecord( mqttContext.outgoingPublishRecords, index3, PACKET_ID, MQTTQoS2, MQTTPubCompPending );
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( PACKET_ID, packetId );
    TEST_ASSERT_EQUAL( index3 + 1, cursor );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, state );

    /* Add another record in #MQTTPubCompPending state. */
    addToRecord( mqttContext.outgoingPublishRecords, index4, PACKET_ID2, MQTTQoS2, MQTTPubCompPending );
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( PACKET_ID2, packetId );
    TEST_ASSERT_EQUAL( index4 + 1, cursor );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, state );

    /* Add another record in #MQTTPubRelSend state. */
    addToRecord( mqttContext.outgoingPublishRecords, index4 + 1, PACKET_ID2 + 1, MQTTQoS2, MQTTPubRelSend );
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( PACKET_ID2 + 1, packetId );
    TEST_ASSERT_EQUAL( index4 + 2, cursor );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, state );

    /* Only one record in #MQTTPubRelSend state. */
    resetPublishRecords( &mqttContext );
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    addToRecord( mqttContext.outgoingPublishRecords, index3, PACKET_ID, MQTTQoS2, MQTTPubRelSend );
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( PACKET_ID, packetId );
    TEST_ASSERT_EQUAL( index3 + 1, cursor );
    TEST_ASSERT_EQUAL( MQTTPubRelSend, state );

    /* Further search should be return no valid packets. */
    state = MQTTStateNull;
    packetId = MQTT_PubrelToResend( &mqttContext, &cursor, &state );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    TEST_ASSERT_EQUAL( MQTTStateNull, state );
    TEST_ASSERT_EQUAL( MQTT_STATE_ARRAY_MAX_COUNT, cursor );
}

void test_MQTT_PublishToResend( void )
{
    MQTTContext_t mqttContext = { 0 };
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    MQTTPublishState_t state = MQTTStateNull;
    uint16_t packetId;
    const uint16_t PACKET_ID = 1;
    const uint16_t PACKET_ID2 = 2;
    const uint16_t PACKET_ID3 = 3;
    const uint16_t PACKET_ID4 = 4;
    const size_t index = 0;
    const size_t index2 = 1;
    const size_t index3 = MQTT_STATE_ARRAY_MAX_COUNT / 2;
    const size_t index4 = index3 + 2;


    /* Invalid parameters. */
    packetId = MQTT_PublishToResend( NULL, &cursor );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    packetId = MQTT_PublishToResend( &mqttContext, NULL );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );

    /* No packet exists. */
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    packetId = MQTT_PublishToResend( &mqttContext, &cursor );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    TEST_ASSERT_EQUAL( MQTT_STATE_ARRAY_MAX_COUNT, cursor );

    /* No packet exists in state #MQTTPublishSend, #MQTTPubAckPending and
     * #MQTTPubRecPending states. */
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    addToRecord( mqttContext.outgoingPublishRecords, index, PACKET_ID3, MQTTQoS2, MQTTPubCompPending );
    addToRecord( mqttContext.outgoingPublishRecords, index2, PACKET_ID4, MQTTQoS2, MQTTPubRelSend );
    packetId = MQTT_PublishToResend( &mqttContext, &cursor );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    TEST_ASSERT_EQUAL( MQTT_STATE_ARRAY_MAX_COUNT, cursor );

    /* Add a record in #MQTTPublishSend state. */
    cursor = MQTT_STATE_CURSOR_INITIALIZER;
    addToRecord( mqttContext.outgoingPublishRecords, index3, PACKET_ID, MQTTQoS2, MQTTPublishSend );
    packetId = MQTT_PublishToResend( &mqttContext, &cursor );
    TEST_ASSERT_EQUAL( PACKET_ID, packetId );
    TEST_ASSERT_EQUAL( index3 + 1, cursor );

    /* Add another record in #MQTTPubAckPending state. */
    addToRecord( mqttContext.outgoingPublishRecords, index4, PACKET_ID2, MQTTQoS1, MQTTPubAckPending );
    packetId = MQTT_PublishToResend( &mqttContext, &cursor );
    TEST_ASSERT_EQUAL( PACKET_ID2, packetId );
    TEST_ASSERT_EQUAL( index4 + 1, cursor );

    /* Add another record in #MQTTPubRecPending state. */
    addToRecord( mqttContext.outgoingPublishRecords, index4 + 1, PACKET_ID2 + 1, MQTTQoS2, MQTTPubRecPending );
    packetId = MQTT_PublishToResend( &mqttContext, &cursor );
    TEST_ASSERT_EQUAL( PACKET_ID2 + 1, packetId );
    TEST_ASSERT_EQUAL( index4 + 2, cursor );

    /* Further search should find no packets. */
    packetId = MQTT_PublishToResend( &mqttContext, &cursor );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, packetId );
    TEST_ASSERT_EQUAL( MQTT_STATE_ARRAY_MAX_COUNT, cursor );
}

/* ========================================================================== */

void test_MQTT_State_strerror( void )
{
    MQTTPublishState_t state;
    const char * str = NULL;

    state = MQTTStateNull;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTStateNull", str );

    state = MQTTPublishSend;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPublishSend", str );

    state = MQTTPubAckSend;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubAckSend", str );

    state = MQTTPubRecSend;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubRecSend", str );

    state = MQTTPubRelSend;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubRelSend", str );

    state = MQTTPubCompSend;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubCompSend", str );

    state = MQTTPubAckPending;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubAckPending", str );

    state = MQTTPubRecPending;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubRecPending", str );

    state = MQTTPubRelPending;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubRelPending", str );

    state = MQTTPubCompPending;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPubCompPending", str );

    state = MQTTPublishDone;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "MQTTPublishDone", str );

    state = MQTTPublishDone + 1;
    str = MQTT_State_strerror( state );
    TEST_ASSERT_EQUAL_STRING( "Invalid MQTT State", str );
}

/* ========================================================================== */
