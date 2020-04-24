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

#include "mqtt_state.h"

#define MQTT_PACKET_ID_INVALID ( uint16_t ) 0U

/**
 * @brief Test if a transition to new state is possible, when dealing with PUBLISHes.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] qos 0, 1, or 2.
 *
 * @note This function does not validate the current state, or the new state
 * based on either the operation type or QoS. It assumes the new state is valid
 * given the opType and QoS, which will be the case if calculated by
 * MQTT_CalculateStatePublish().
 *
 * @return `true` if transition is possible, else `false`
 */
static bool _validateTransitionPublish( MQTTPublishState_t currentState,
                                        MQTTPublishState_t newState,
                                        MQTTStateOperation_t opType,
                                        MQTTQoS_t qos );

/**
 * @brief Test if a transition to a new state is possible, when dealing with acks.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 *
 * @return `true` if transition is possible, else `false`.
 */
static bool _validateTransitionAck( MQTTPublishState_t currentState,
                                    MQTTPublishState_t newState );

/**
 * @brief Test if the publish corresponding to an ack is outgoing or incoming.
 *
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send, or Receive.
 *
 * @return `true` if corresponds to outgoing publish, else `false`.
 */
static bool _isPublishOutgoing( MQTTPubAckType_t packetType,
                                MQTTStateOperation_t opType );

/**
 * @brief Find a packet ID in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] packetId packet ID to search for.
 * @param[out] pQos QoS retrieved from record.
 * @param[out] pCurrentState state retrieved from record.
 *
 * @return index of the packet id in the record if it exists, else the record length.
 */
static size_t _findInRecord( const MQTTPubAckInfo_t * records,
                             size_t recordLen,
                             uint16_t packetId,
                             MQTTQoS_t * pQos,
                             MQTTPublishState_t * pCurrentState );

/**
 * @brief Delete an entry from the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] index Index of record to delete.
 *
 * @return MQTTSuccess if successful, else MQTTBadParameter.
 */
static MQTTStatus_t _deleteRecord( MQTTPubAckInfo_t * records,
                                   size_t recordLen,
                                   size_t index );

/**
 * @brief Store a new entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] packetId, packet ID of new entry.
 * @param[in] qos QoS of new entry.
 * @param[in] publishState state of new entry.
 *
 * @return MQTTSuccess, MQTTNoMemory, MQTTStateCollision, or MQTTBadParameter.
 */
static MQTTStatus_t _addRecord( MQTTPubAckInfo_t * records,
                                size_t recordLen,
                                uint16_t packetId,
                                MQTTQoS_t qos,
                                MQTTPublishState_t publishState );

/**
 * @brief Update and possibly delete an entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] recordIndex index of record to update.
 * @param[in] newState New state to update.
 * @param[in] shouldDelete Whether an existing entry should be deleted.
 *
 * @return MQTTSuccess or MQTTBadParameter.
 */
static MQTTStatus_t _updateRecord( MQTTPubAckInfo_t * records,
                                   size_t recordLen,
                                   size_t recordIndex,
                                   MQTTPublishState_t newState,
                                   bool shouldDelete );


static bool _validateTransitionPublish( MQTTPublishState_t currentState,
                                        MQTTPublishState_t newState,
                                        MQTTStateOperation_t opType,
                                        MQTTQoS_t qos )
{
    bool isValid = false;
    switch( currentState )
    {
        case MQTTStateNull:
            /* Transitions from invalid occur when storing a new entry into the record. */
            if( opType == MQTT_RECEIVE )
            {
                isValid = ( newState == MQTTPubAckSend ) || ( newState == MQTTPubRecSend );
            }
            break;
        case MQTTPublishSend:
            /* Outgoing publish. */
            switch( qos )
            {
                case MQTTQoS0:
                    isValid = ( newState == MQTTPublishDone );
                    break;
                case MQTTQoS1:
                    isValid = ( newState == MQTTPubAckPending );
                    break;
                case MQTTQoS2:
                    isValid = ( newState == MQTTPubRecPending );
                    break;
                default:
                    /* No other QoS value. */
                    break;
            }
            break;
        default:
            /* For a PUBLISH, we should not start from any other state. */
            break;
    }
    return isValid;
}

static bool _validateTransitionAck( MQTTPublishState_t currentState,
                                    MQTTPublishState_t newState )
{
    bool isValid = false;
    switch( currentState )
    {
        case MQTTPubAckSend:
            /* Incoming publish, QoS 1. */
            isValid = ( newState == MQTTPublishDone );
        case MQTTPubAckPending:
            /* Outgoing publish, QoS 1. */
            isValid = ( newState == MQTTPublishDone );
            break;
        case MQTTPubRecSend:
            /* Incoming publish, QoS 2. */
            isValid = ( newState == MQTTPubRelPending );
            break;
        case MQTTPubRelPending:
            /* Incoming publish, QoS 2. */
            isValid = ( newState == MQTTPubCompSend );
            break;
        case MQTTPubCompSend:
            /* Incoming publish, QoS 2. */
            isValid = ( newState == MQTTPublishDone );
            break;
        case MQTTPubRecPending:
            /* Outgoing publish, Qos 2. */
            isValid = ( newState == MQTTPubRelSend );
            break;
        case MQTTPubRelSend:
            /* Outgoing publish, Qos 2. */
            isValid = ( newState == MQTTPubCompPending );
            break;
        case MQTTPubCompPending:
            /* Outgoing publish, Qos 2. */
            isValid = ( newState == MQTTPublishDone );
            break;
        case MQTTPublishDone:
            /* Done state should transition to invalid since it will be removed from the record. */
        case MQTTPublishSend:
            /* If an ack was sent/received we shouldn't have been in this state. */
        case MQTTStateNull:
            /* If an ack was sent/received the record should exist. */
        default:
            /* Invalid. */
            break;
    }

    return isValid;
}

static bool _isPublishOutgoing( MQTTPubAckType_t packetType,
                                MQTTStateOperation_t opType )
{
    bool isOutgoing = false;
    switch( packetType )
    {
        case MQTTPuback:
            isOutgoing = ( opType == MQTT_RECEIVE );
            break;
        case MQTTPubrec:
            isOutgoing = ( opType == MQTT_RECEIVE );
            break;
        case MQTTPubrel:
            isOutgoing = ( opType == MQTT_SEND );
            break;
        case MQTTPubcomp:
            isOutgoing = ( opType == MQTT_RECEIVE );
            break;
        default:
            /* No other ack type. */
            break;
    }
    return isOutgoing;
}

static size_t _findInRecord( const MQTTPubAckInfo_t * records,
                             size_t recordLen,
                             uint16_t packetId,
                             MQTTQoS_t * pQos,
                             MQTTPublishState_t * pCurrentState )
{
    size_t index = 0;
    *pCurrentState = MQTTStateNull;
    if( packetId == MQTT_PACKET_ID_INVALID )
    {
        index = recordLen;
    }
    else
    {
        for( index = 0; index < recordLen; index++ )
        {
            if( records[ index ].packetId == packetId )
            {
                *pQos = records[ index ].qos;
                *pCurrentState = records[ index ].publishState;
                break;
            }
        }
    }
    return index;
}

static MQTTStatus_t _deleteRecord( MQTTPubAckInfo_t * records,
                                   size_t recordLen,
                                   size_t index )
{
    MQTTStatus_t status = MQTTSuccess;
    if( index < recordLen )
    {
        records[ index ].packetId = MQTT_PACKET_ID_INVALID;
        records[ index ].qos = MQTTQoS0;
        records[ index ].publishState = MQTTStateNull;
    }
    else
    {
        /* Out of bounds error. */
        status = MQTTBadParameter;
    }
    return status;
}

static MQTTStatus_t _addRecord( MQTTPubAckInfo_t * records,
                                size_t recordLen,
                                uint16_t packetId,
                                MQTTQoS_t qos,
                                MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTNoMemory;
    int index = 0;
    size_t availableIndex = recordLen;
    if( packetId == MQTT_PACKET_ID_INVALID || qos == MQTTQoS0 )
    {
        status = MQTTBadParameter;
    }
    else
    {
        /* Start from end so first available index will be populated. */
        for( index = recordLen - 1; index >= 0; index-- )
        {
            if( records[ index ].packetId == MQTT_PACKET_ID_INVALID )
            {
                availableIndex = index;
            }
            else if( records[ index ].packetId == packetId )
            {
                /* Collision. */
                status = MQTTStateCollision;
                availableIndex = recordLen;
                break;
            }
            else
            {
                /* Empty else clause. */
            }   
        }
    }

    if( availableIndex < recordLen )
    {
        records[ availableIndex ].packetId = packetId;
        records[ availableIndex ].qos = qos;
        records[ availableIndex ].publishState = publishState;
        status = MQTTSuccess;
    }

    return status;
}

static MQTTStatus_t _updateRecord( MQTTPubAckInfo_t * records,
                                   size_t recordLen,
                                   size_t recordIndex,
                                   MQTTPublishState_t newState,
                                   bool shouldDelete )
{
    MQTTStatus_t status = MQTTBadParameter;

    if( recordIndex < recordLen )
    {
        if( shouldDelete )
        {
            status = _deleteRecord( records, recordLen, recordIndex );
        }
        else
        {
            records[ recordIndex ].publishState = newState;
            status = MQTTSuccess;
        }
    }
    
    return status;
}

MQTTPublishState_t MQTT_ReserveState( MQTTContext_t * pMqttContext,
                                      uint16_t packetId,
                                      MQTTQoS_t qos )
{
    MQTTPublishState_t state = MQTTStateNull;
    MQTTQoS_t tempQoS = MQTTQoS0;
    MQTTPublishState_t tempState = MQTTStateNull;
    size_t recordIndex = MQTT_MAX_QUEUED_PUBLISH_MESSAGES;
    MQTTStatus_t mqttStatus = MQTTBadParameter;

    recordIndex = _findInRecord( pMqttContext->outgoingPublishRecords,
                                 MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                 packetId,
                                 &tempQoS,
                                 &tempState );

    /* Make sure there's no collision. */
    if( recordIndex >= MQTT_MAX_QUEUED_PUBLISH_MESSAGES )
    {
        mqttStatus = _addRecord( pMqttContext->outgoingPublishRecords,
                                 MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                 packetId,
                                 qos,
                                 MQTTPublishSend );
    }

    if( mqttStatus != MQTTSuccess )
    {
        state = MQTTStateNull;
    }
    else
    {
        state = MQTTPublishSend;
    }
    
    return state;
}

MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos )
{
    MQTTPublishState_t calculatedState = MQTTStateNull;
    switch( qos )
    {
        case MQTTQoS0:
            calculatedState = MQTTPublishDone;
            break;
        case MQTTQoS1:
            calculatedState = ( opType == MQTT_SEND )? MQTTPubAckPending : MQTTPubAckSend;
            break;
        case MQTTQoS2:
            calculatedState = ( opType == MQTT_SEND )? MQTTPubRecPending : MQTTPubRecSend;
            break;
        default:
            /* No other QoS values. */
            break;
    }
    return calculatedState;
}

MQTTPublishState_t MQTT_UpdateStatePublish( MQTTContext_t * pMqttContext,
                                            uint16_t packetId,
                                            MQTTStateOperation_t opType,
                                            MQTTQoS_t receivedQoS )
{
    MQTTPublishState_t newState = MQTTStateNull;
    MQTTPublishState_t currentState = MQTTStateNull;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    size_t recordIndex = MQTT_MAX_QUEUED_PUBLISH_MESSAGES;
    MQTTQoS_t qos = MQTTQoS0;
    MQTTPubAckInfo_t * records = NULL;
    bool isTransitionValid = false;

    /* Set this pointer so some common code can be used later. */
    if( opType == MQTT_SEND )
    {
        records = pMqttContext->outgoingPublishRecords;
    }
    else
    {
        records = pMqttContext->incomingPublishRecords;
    }
    

    if( packetId == MQTT_PACKET_ID_INVALID )
    {
        /* QoS 0 publish. Do nothing. */
        newState = MQTTPublishDone;
    }
    else
    {
        recordIndex = _findInRecord( records,
                                     MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                     packetId,
                                     &qos,
                                     &currentState );
        /* When the record does not exist, a QoS must be supplied. Otherwise,
         * we ignore it. */
        if( opType == MQTT_RECEIVE )
        {
            qos = receivedQoS;
        }
        newState = MQTT_CalculateStatePublish( opType, qos );
        isTransitionValid = _validateTransitionPublish( currentState, newState, opType, qos );
        if( opType == MQTT_SEND )
        {
            if( isTransitionValid && recordIndex < MQTT_MAX_QUEUED_PUBLISH_MESSAGES )
            {
                mqttStatus = _updateRecord( records,
                                            MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                            recordIndex,
                                            newState,
                                            false );
            }
        }
        else
        {
            if( isTransitionValid && recordIndex >= MQTT_MAX_QUEUED_PUBLISH_MESSAGES )
            {
                mqttStatus = _addRecord( records,
                                         MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                         packetId,
                                         qos,
                                         newState );
            }
        }
        if( mqttStatus != MQTTSuccess )
        {
            newState = MQTTStateNull;
        }
    }
    
    return newState;
}

MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos )
{
    MQTTPublishState_t calculatedState = MQTTStateNull;
    /* There are more QoS2 cases than QoS1, so initialize to that. */
    bool qosValid = ( qos == MQTTQoS2 );

    switch( packetType )
    {
        case MQTTPuback:
            qosValid = ( qos == MQTTQoS1 );
            calculatedState = MQTTPublishDone;
            break;
        case MQTTPubrec:
            /* Incoming publish: send PUBREC, PUBREL pending.
             * Outgoing publish: receive PUBREC, send PUBREL. */
            calculatedState = ( opType == MQTT_SEND )? MQTTPubRelPending : MQTTPubRelSend;
            break;
        case MQTTPubrel:
            /* Incoming publish: receive PUBREL, send PUBCOMP.
             * Outgoing publish: send PUBREL, PUBCOMP pending. */
            calculatedState = ( opType == MQTT_SEND )? MQTTPubCompPending : MQTTPubCompSend;
        case MQTTPubcomp:
            calculatedState = MQTTPublishDone;
            break;
        default:
            break;
    }
    /* Sanity check, make sure ack and QoS agree. */
    if( !qosValid )
    {
        calculatedState = MQTTStateNull;
    }
    return calculatedState;
}

MQTTPublishState_t MQTT_UpdateStateAck( MQTTContext_t * pMqttContext,
                                        uint16_t packetId,
                                        MQTTPubAckType_t packetType,
                                        MQTTStateOperation_t opType )
{
    MQTTPublishState_t newState = MQTTStateNull;
    MQTTPublishState_t currentState = MQTTStateNull;
    MQTTStatus_t mqttStatus = MQTTIllegalState;
    bool isPublishOutgoing = _isPublishOutgoing( packetType, opType );
    bool shouldDeleteRecord = false;
    bool isTransitionValid = false;
    MQTTQoS_t qos = MQTTQoS0;
    size_t recordIndex = MQTT_MAX_QUEUED_PUBLISH_MESSAGES;
    MQTTPubAckInfo_t * records = NULL;

    if( isPublishOutgoing )
    {
        records = pMqttContext->outgoingPublishRecords;
    }
    else
    {
        records = pMqttContext->incomingPublishRecords;
    }
    recordIndex = _findInRecord( records,
                                 MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                 packetId,
                                 &qos,
                                 &currentState );

    if( recordIndex < MQTT_MAX_QUEUED_PUBLISH_MESSAGES )
    {
        newState = MQTT_CalculateStateAck( packetType, opType, qos );
        shouldDeleteRecord = ( newState == MQTTPublishDone );
        isTransitionValid = _validateTransitionAck( currentState, newState );
        if( isTransitionValid )
        {
            mqttStatus = _updateRecord( records,
                                        MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                        recordIndex,
                                        newState,
                                        shouldDeleteRecord );

            if( mqttStatus != MQTTSuccess )
            {
                newState = MQTTStateNull;
            }
        }
        else
        {
            newState = MQTTStateNull;
        }
        
    }
    return newState;
}
