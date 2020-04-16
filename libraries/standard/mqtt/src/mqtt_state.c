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

#define MQTT_PACKET_ID_INVALID ( uint16_t ) 0

/**
 * @brief Set the appropriate state when the packet is one of PUBACK,
 * PUBREC, PUBREL, or PUBCOMP.
 * 
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] idStatus Invalid, Unknown, or Known.
 * @param[in] sendState The state to set for a SEND operation.
 * @param[in] recvState The state to set for a RECEIVE operation.
 * 
 * @return The calculated state, which is one of MQTTInvalidState, `sendState`,
 * or `recvState`.
 */
static MQTTPublishState_t _calculateAckState( MQTTStateOperation_t opType,
                                              MQTTPacketIDState_t idStatus,
                                              MQTTPublishState_t sendState,
                                              MQTTPublishState_t recvState );

/**
 * @brief Calculate a state when QoS is 1.
 *
 * @param[in] packetType PUBLISH or PUBACK.
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] idStatus Invalid, Unknown, or Known.
 *
 * @return The calculated state.
 */
static MQTTPublishState_t _calculateQoS1( MQTTPublishType_t packetType,
                                          MQTTStateOperation_t opType,
                                          MQTTPacketIDState_t idStatus );

/**
 * @brief Calculate a state when QoS is 2.
 *
 * @param[in] packetType PUBLISH, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] idStatus Invalid, Unknown, or Known.
 *
 * @return The calculated state.
 */
static MQTTPublishState_t _calculateQoS2( MQTTPublishType_t packetType,
                                          MQTTStateOperation_t opType,
                                          MQTTPacketIDState_t idStatus );

/**
 * @brief Test if a transition to new state is possible.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] qos 0, 1, or 2.
 *
 * @note This function does not validate the current state, or the new state
 * based on either the operation type or QoS. It assumes the new state is valid
 * given the opType and QoS, which will be the case if calculated by
 * _MQTT_CalculateState().
 *
 * @return `true` if transition is possible, else `false`
 */
static bool _validateTransition( MQTTPublishState_t currentState,
                                 MQTTPublishState_t newState,
                                 MQTTStateOperation_t opType,
                                 MQTTQoS_t qos );

/**
 * @brief Test is a publish is outgoing or incoming.
 *
 * @param[in] packetType PUBLISH, PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Reserve, Send, or Receive.
 *
 * @return `true` if outgoing publish, else `false`
 */
static bool _isPublishOutgoing( MQTTPublishType_t packetType,
                                MQTTStateOperation_t opType );

/**
 * @brief Reconcile a supplied QoS with one looked up from the record.
 *
 * @param[in] inputQoS 0, 1, 2, or INVALID.
 * @param[in, out] pFoundQoS QoS retrieved from record.
 *
 * @return MQTTBadParameter if error; else MQTTSuccess.
 */
static MQTTStatus_t _resolveQoS( MQTTQoS_t inputQoS,
                                 MQTTQoS_t * pFoundQoS );

/**
 * @brief Find a packet ID in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] packetId packet ID to search for.
 * @param[out] pIdStatus invalid if packet ID is 0, Known if packet ID exists
 * in record, else Unknown.
 * @param[out] pQos QoS retrieved from record.
 * @param[out] pCurrentState state retrieved from record.
 *
 * @return index of the packet id in the record if it exists, else the record length.
 */
static uint16_t _findInRecord( const MQTTPubAckInfo_t * records,
                               size_t recordLen,
                               uint16_t packetId,
                               MQTTPacketIDState_t * pIdStatus,
                               MQTTQoS_t * pQos,
                               MQTTPublishState_t * pCurrentState );

/**
 * @brief Delete an entry from the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] index Index of record to delete.
 *
 * @return MQTTSuccess if successful, else MQTTBadParameter
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
 * @brief Add, delete, or update an entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordLen Length of record.
 * @param[in] recordIndex index of record to update.
 * @param[in] packetId ID of packet to update.
 * @param[in] qos QoS of record to update.
 * @param[in] newState New state to update.
 * @param[in] shouldStore Whether a new entry should be added to the record.
 * @param[in] shouldDelete Whether an existing entry should be deleted.
 *
 * @note If adding an entry then `recordIndex` is ignored. If deleting an entry
 * then `qos`, `packetId`, and `newState` are ignored. If updating an entry,
 * then `qos`, and `packetId` are used for validation.
 * @return MQTTSuccess, MQTTNoMemory, MQTTStateCollision, or MQTTBadParameter
 */
static MQTTStatus_t _updateRecord( MQTTPubAckInfo_t * records,
                                   size_t recordLen,
                                   size_t recordIndex,
                                   uint16_t packetId,
                                   MQTTQoS_t qos,
                                   MQTTPublishState_t newState,
                                   bool shouldStore,
                                   bool shouldDelete );




static MQTTPublishState_t _calculateAckState( MQTTStateOperation_t opType,
                                              MQTTPacketIDState_t idStatus,
                                              MQTTPublishState_t sendState,
                                              MQTTPublishState_t recvState )
{
    MQTTPublishState_t calculatedState = MQTTInvalidState;
    switch( opType )
    {
        case MQTT_SEND:
            if( idStatus == ID_KNOWN )
            {
                calculatedState = sendState;
            }
            break;
        case MQTT_RECEIVE:
            if( idStatus == ID_KNOWN )
            {
                calculatedState = recvState;
            }
            break;
        case MQTT_RESERVE:
            /* We should not be reserving for an ack. */
        default:
            break;
    }
    return calculatedState;
}

static MQTTPublishState_t _calculateQoS1( MQTTPublishType_t packetType,
                                          MQTTStateOperation_t opType,
                                          MQTTPacketIDState_t idStatus )
{
    MQTTPublishState_t calculatedState = MQTTInvalidState;
    switch( packetType )
    {
        case MQTT_PUBLISH:
            switch( opType )
            {
                case MQTT_RESERVE:
                    /* Outgoing publish. */
                    if( idStatus == ID_UNKNOWN )
                    {
                        calculatedState = MQTTPublishSend;
                    }
                    break;
                case MQTT_SEND:
                    /* Outgoing publish. */
                    if( idStatus == ID_KNOWN )
                    {
                        calculatedState = MQTTPubAckPending;
                    }
                    break;
                case MQTT_RECEIVE:
                    /* Incoming publish. */
                    if( idStatus == ID_UNKNOWN )
                    {
                        calculatedState = MQTTPubAckSend;
                    }
                    break;
                default:
                    break;
            }
            break;
        case MQTT_PUBACK:
            calculatedState = _calculateAckState( opType, idStatus, MQTTPublishDone, MQTTPublishDone );
            break;
        default:
            /* Any packet type besides PUBLISH or PUBACK is invalid for QoS 1. */
            break;
    }
    return calculatedState;
}

static MQTTPublishState_t _calculateQoS2( MQTTPublishType_t packetType,
                                          MQTTStateOperation_t opType,
                                          MQTTPacketIDState_t idStatus )
{
    MQTTPublishState_t calculatedState = MQTTInvalidState;
    switch( packetType )
    {
        case MQTT_PUBLISH:
            switch( opType )
            {
                case MQTT_RESERVE:
                    if( idStatus == ID_UNKNOWN )
                    {
                        calculatedState = MQTTPublishSend;
                    }
                    break;
                case MQTT_SEND:
                    if( idStatus == ID_KNOWN )
                    {
                        calculatedState = MQTTPubRecPending;
                    }
                    break;
                case MQTT_RECEIVE:
                    if( idStatus == ID_UNKNOWN )
                    {
                        calculatedState = MQTTPubRecSend;
                    }
                    break;
                default:
                    break;
            }
            break;
        case MQTT_PUBREC:
            /* Incoming publish: send PUBREC, PUBREL pending.
             * Outgoing publish: receive PUBREC, send PUBREL. */
            calculatedState = _calculateAckState( opType, idStatus, MQTTPubRelPending, MQTTPubRelSend );
            break;
        case MQTT_PUBREL:
            /* Incoming publish: receive PUBREL, send PUBCOMP.
             * Outgoing publish: send PUBREL, PUBCOMP pending. */
            calculatedState = _calculateAckState( opType, idStatus, MQTTPubCompPending, MQTTPubCompSend );
            break;
        case MQTT_PUBCOMP:
            calculatedState = _calculateAckState( opType, idStatus, MQTTPublishDone, MQTTPublishDone );
            break;
        default:
            /* Other packet types are invalid for QoS 2. */
            break;
    }
    return calculatedState;
}

static bool _validateTransition( MQTTPublishState_t currentState,
                                 MQTTPublishState_t newState,
                                 MQTTStateOperation_t opType,
                                 MQTTQoS_t qos )
{
    bool isValid = false;
    switch( currentState )
    {
        case MQTTInvalidState:
            /* Transitions from invalid occur when storing a new entry into the record. */
            switch( opType )
            {
                case MQTT_RESERVE:
                    /* Outgoing publishes. */
                    isValid = ( newState == MQTTPublishSend );
                    break;
                case MQTT_RECEIVE:
                    /* Incoming publishes. */
                    isValid = ( newState == MQTTPubAckSend ) || ( newState == MQTTPubRecSend );
                    break;
                case MQTT_SEND:
                default:
                    break;
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
                    break;
            }
            break;
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
        default:
            break;
    }
    return isValid;
}

static bool _isPublishOutgoing( MQTTPublishType_t packetType,
                                MQTTStateOperation_t opType )
{
    bool isOutgoing = false;
    switch( packetType )
    {
        case MQTT_PUBLISH:
            isOutgoing = ( ( opType == MQTT_RESERVE ) || ( opType == MQTT_SEND ) );
            break;
        case MQTT_PUBACK:
            isOutgoing = ( opType == MQTT_RECEIVE );
            break;
        case MQTT_PUBREC:
            isOutgoing = ( opType == MQTT_RECEIVE );
            break;
        case MQTT_PUBREL:
            isOutgoing = ( opType == MQTT_SEND );
            break;
        case MQTT_PUBCOMP:
            isOutgoing = ( opType == MQTT_RECEIVE );
            break;
        default:
            break;
    }
    return isOutgoing;
}

static MQTTStatus_t _resolveQoS( MQTTQoS_t inputQoS,
                                 MQTTQoS_t * pFoundQoS )
{
    MQTTStatus_t status = MQTTSuccess;

    if( inputQoS != MQTTInvalidQoS )
    {
        if( *pFoundQoS == MQTTInvalidQoS )
        {
            *pFoundQoS = inputQoS;
        }
        else if( *pFoundQoS != inputQoS )
        {
            /* Supplied QoS and record don't match. */
            status = MQTTBadParameter;
        }
        else
        {
            /* Empty else clause. */
        }
    }
    if( *pFoundQoS == MQTTInvalidQoS )
    {
        /* Treat invalid the same as QoS 0 since it won't be stored in state record. */
        *pFoundQoS = MQTTQoS0;
    }

    return status;
}

static uint16_t _findInRecord( const MQTTPubAckInfo_t * records,
                               size_t recordLen,
                               uint16_t packetId,
                               MQTTPacketIDState_t * pIdStatus,
                               MQTTQoS_t * pQos,
                               MQTTPublishState_t * pCurrentState )
{
    uint16_t index = 0;
    *pCurrentState = MQTTInvalidState;
    if( packetId == MQTT_PACKET_ID_INVALID )
    {
        *pIdStatus = ID_INVALID;
        index = recordLen;
    }
    else
    {
        *pIdStatus = ID_UNKNOWN;
        for( index = 0; index < recordLen; index++ )
        {
            if( records[ index ].packetId == packetId )
            {
                *pIdStatus = ID_KNOWN;
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
        records[ index ].publishState = MQTTInvalidState;
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
                                   uint16_t packetId,
                                   MQTTQoS_t qos,
                                   MQTTPublishState_t newState,
                                   bool shouldStore,
                                   bool shouldDelete )
{
    MQTTStatus_t status = MQTTSuccess;
    if( shouldStore )
    {
        status = _addRecord( records,
                             recordLen,
                             packetId,
                             qos,
                             newState );
    }
    else if( recordIndex >= recordLen )
    {
        /* Something's wrong because the record should exist. */
        status = MQTTBadParameter;
    }
    else if( shouldDelete )
    {
        status = _deleteRecord( records,
                                recordLen,
                                recordIndex );
    }
    else
    {
        /* Sanity checks. */
        if( records[ recordIndex ].packetId != packetId )
        {
            status = MQTTBadParameter;
        }
        else if( records[ recordIndex ].qos != qos )
        {
            status = MQTTBadParameter;
        }
        else
        {
            records[ recordIndex ].publishState = newState;
        }
    }
    
    return status;
}

MQTTPublishState_t _MQTT_CalculateState( MQTTPublishType_t packetType,
                                         MQTTStateOperation_t opType,
                                         MQTTQoS_t qos,
                                         MQTTPacketIDState_t idStatus )
{
    MQTTPublishState_t calculatedState = MQTTInvalidState;
    switch( qos )
    {
        case MQTTQoS0:
            if( idStatus == ID_UNKNOWN && packetType == MQTT_PUBLISH )
            {
                if( opType == MQTT_RESERVE )
                {
                    calculatedState = MQTTPublishSend;
                }
                else /* Sent or received. */
                {
                    calculatedState = MQTTPublishDone;
                }
            }
            /* Anything else is an error. */
            break;
        case MQTTQoS1:
            calculatedState = _calculateQoS1( packetType, opType, idStatus );
            break;
        case MQTTQoS2:
            calculatedState = _calculateQoS2( packetType, opType, idStatus );
            break;
        default:
            break;
    }
    return calculatedState;
}

MQTTStatus_t _MQTT_UpdateState( MQTTContext_t * pMqttContext,
                                uint16_t packetId,
                                MQTTPublishType_t packetType,
                                MQTTStateOperation_t opType,
                                MQTTQoS_t qos )
{
    MQTTStatus_t status = MQTTSuccess;
    bool isPublishOutgoing = _isPublishOutgoing( packetType, opType );
    bool shouldStoreRecord = false;
    bool shouldDeleteRecord = false;
    bool isTransitionValid = false;
    MQTTPacketIDState_t idStatus = ID_INVALID;
    MQTTPublishState_t currentState = MQTTInvalidState;
    MQTTPublishState_t newState = MQTTInvalidState;
    MQTTQoS_t foundQoS = MQTTInvalidQoS;
    uint16_t recordIndex = MQTT_MAX_QUEUED_PUBLISH_MESSAGES;
    MQTTPubAckInfo_t * records = NULL, * oppositeRecords = NULL;

    if( isPublishOutgoing )
    {
        records = pMqttContext->outgoingPublishRecords;
        oppositeRecords = pMqttContext->incomingPublishRecords;
    }
    else
    {
        records = pMqttContext->incomingPublishRecords;
        oppositeRecords = pMqttContext->outgoingPublishRecords;
    }
    
    /* Check the opposite array first for a collision. */
    recordIndex = _findInRecord( oppositeRecords,
                                 MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                 packetId,
                                 &idStatus,
                                 &foundQoS,
                                 &currentState );

    if( idStatus == ID_KNOWN )
    {
        /* Collision. */
        status = MQTTStateCollision;
    }
    else
    {
        /* Reset to invalid. */
        currentState = MQTTInvalidState;
        foundQoS = MQTTInvalidQoS;
        idStatus = ID_INVALID;
        recordIndex = MQTT_MAX_QUEUED_PUBLISH_MESSAGES;
    }

    recordIndex = _findInRecord( records,
                                 MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                 packetId,
                                 &idStatus,
                                 &foundQoS,
                                 &currentState );

    /* Resolve QoS between supplied and found. */
    if( status == MQTTSuccess )
    {
        /* Reconcile the supplied QoS with the one in the record. */
        status = _resolveQoS( qos, &foundQoS );
    }

    if( status == MQTTSuccess )
    {
        newState = _MQTT_CalculateState( packetType, opType, foundQoS, idStatus );

        if( newState == MQTTInvalidState )
        {
            status = MQTTIllegalState;
            /* Test if collision. */
            if( opType == MQTT_RESERVE && idStatus == ID_KNOWN )
            {
                status = MQTTStateCollision;
            }
        }
    }
    if( status == MQTTSuccess )
    {
        if( foundQoS != MQTTQoS0 )
        {
            shouldStoreRecord = ( newState == MQTTPublishSend ) ||
                                ( newState == MQTTPubAckSend ) ||
                                ( newState == MQTTPubRecSend );
            shouldDeleteRecord = ( newState == MQTTPublishDone );
        }

        isTransitionValid = _validateTransition( currentState, newState, opType, foundQoS );

        if( !isTransitionValid )
        {
            status = MQTTIllegalState;
        }
        else if( foundQoS != MQTTQoS0 )
        {
            /* Update the state record. */
            status = _updateRecord( records,
                                    MQTT_MAX_QUEUED_PUBLISH_MESSAGES,
                                    recordIndex,
                                    packetId,
                                    foundQoS,
                                    newState,
                                    shouldStoreRecord,
                                    shouldDeleteRecord );
        }
        else
        {
            /* QoS 0, do nothing. */
        }
    }
    
    return status;
}
