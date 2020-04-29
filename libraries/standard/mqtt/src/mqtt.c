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

#include <string.h>
#include <assert.h>

#include "mqtt.h"
#include "mqtt_state.h"
#include "private/mqtt_internal.h"

/*-----------------------------------------------------------*/

/**
 * @brief Sends provided buffer to network using transport send.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pBufferToSend Buffer to be sent to network.
 * @brief param[in] bytesToSend Number of bytes to be sent.
 *
 * @return Total number of bytes sent; -1 if there is an error.
 */
static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend );

/**
 * @brief Validates parameters of #MQTT_Subscribe or #MQTT_Unsubscribe.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId Packet identifier.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * const pContext,
                                                        const MQTTSubscribeInfo_t * const pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId );

/**
 * @brief Send serialized publish packet using transport send.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] headerSize Header size of the PUBLISH packet.
 *
 * @return #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t sendPublish( const MQTTContext_t * const pContext,
                                 const MQTTPublishInfo_t * const pPublishInfo,
                                 size_t headerSize );

/**
 * @brief Receives a CONNACK MQTT packet.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] timeoutMs Timeout for waiting for CONNACK packet.
 * @param[out] pIncomingPacket List of MQTT subscription info.
 * @param[out] pSessionPresent Whether a previous session was present.
 * Only relevant if not establishing a clean session.
 *
 * @return #MQTTBadResponse if a bad response is received;
 * #MQTTNoDataAvailable if no data available for transport recv;
 * ##MQTTRecvFailed if transport recv failed;
 * #MQTTSuccess otherwise.
 */
static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
                                    uint32_t timeoutMs,
                                    MQTTPacketInfo_t * const pIncomingPacket,
                                    bool * const pSessionPresent );

/**
 * @brief Calculate the interval between two timestamps, including when the
 * later value has overflowed.
 *
 * @param[in] later The later time stamp.
 * @param[in] start The earlier time stamp.
 *
 * @return later - start.
 */
static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start );

/*-----------------------------------------------------------*/

static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend )
{
    const uint8_t * pIndex = pBufferToSend;
    size_t bytesRemaining = bytesToSend;
    int32_t totalBytesSent = 0, bytesSent;
    uint32_t sendTime = 0U;

    assert( pContext != NULL );
    assert( bytesToSend != 0 );

    /* Point to the start of the network buffer from the context. */
    pIndex = pContext->networkBuffer.pBuffer;
    /* Record the time of transmission. */
    sendTime = pContext->callbacks.getTime();
    bytesRemaining = bytesToSend;

    /* Loop until the entire packet is sent. */
    while( bytesRemaining > 0UL )
    {
        bytesSent = pContext->transportInterface.send( pContext->transportInterface.networkContext,
                                                       pIndex,
                                                       bytesRemaining );

        if( bytesSent > 0 )
        {
            bytesRemaining -= ( size_t ) bytesSent;
            totalBytesSent += bytesSent;
            pIndex += bytesSent;
            LogDebugWithArgs( "Bytes sent=%d, bytes remaining=%ul,"
                              "total bytes sent=%d.",
                              bytesSent,
                              bytesRemaining,
                              totalBytesSent );
        }
        else
        {
            LogError( "Transport send failed." );
            totalBytesSent = -1;
            break;
        }
    }

    /* Update time of last transmission if the entire packet was successfully sent. */
    if( totalBytesSent > -1 )
    {
        pContext->lastPacketTime = sendTime;
        LogDebugWithArgs( "Successfully sent packet at time %u.",
                          sendTime );
    }

    return totalBytesSent;
}

/*-----------------------------------------------------------*/
/**
 * @brief Receive a packet from the transport interface.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] incomingPacket packet struct with remaining length.
 *
 * @return MQTTSuccess or MQTTRecvFailed.
 */
static MQTTStatus_t _receivePacket( MQTTContext_t * const pContext,
                                    MQTTPacketInfo_t incomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesReceived = 0;
    int32_t totalBytesReceived = 0;
    size_t bytesToReceive = 0;

    assert( pContext != NULL );

    if( incomingPacket.remainingLength > pContext->networkBuffer.size )
    {
        bytesToReceive = pContext->networkBuffer.size;
        IotLogWarnWithArgs( "Incoming packet length %u exceeds network buffer size %u."
                            "Incoming packet will be dumped",
                            incomingPacket.remainingLength
                            pContext->networkBuffer );
    }
    else
    {
        bytesToReceive = incomingPacket.remainingLength;
    }

    bytesReceived = pContext->transportInterface.recv( pContext->transportInterface.networkContext,
                                                       pContext->networkBuffer.pBuffer,
                                                       bytesToReceive );
    totalBytesReceived = bytesReceived;

    /* Partial receive. */
    if( bytesReceived < ( int32_t ) bytesToReceive )
    {
        IotLogWarnWithArgs( "Packet partially received: Bytes received=%d,"
                            "Bytes expected=%u",
                            bytesReceived,
                            bytesToReceive );
        /* Handle partial receive. */
        bytesReceived = pContext->transportInterface.recv( pContext->transportInterface.networkContext,
                                                           ( pContext->networkBuffer.pBuffer + totalBytesReceived ),
                                                           ( bytesToReceive - totalBytesReceived ) );
        totalBytesReceived += bytesReceived;
        if( totalBytesReceived != ( int32_t ) bytesToReceive )
        {
            IotLogErrorWithArgs( "Handling partial receive failed. Bytes "
                                 "received=%d, Bytes expected=%u",
                                 totalBytesReceived,
                                 bytesToReceive );
            status = MQTTRecvFailed;
        }
    }
    /* Too many bytes received. */
    else if( bytesReceived > ( int32_t ) bytesToReceive )
    {
        IotLogErrorWithArgs( "Too many bytes received. Bytes received=%d, ",
                             "Bytes expected=%u",
                             bytesReceived,
                             bytesToReceive );
        status = MQTTRecvFailed;
    }
    else
    {
        /* Receive successful, bytesReceived == bytesToReceive. */
        IotLogInfoWithArgs( "Packet received. Received bytes=%d",
                            bytesReceived );
    }

    /* Check if packet exceeds buffer. */
    if( ( status == MQTTSuccess ) && ( ( int32_t ) incomingPacket.remainingLength > bytesToReceive ) )
    {
        /* Packet exceeds buffer, dump it. At this point, bytesToReceive is
         * pContext->networkBuffer.size, so we don't need to update it until
         * the end of the loop. */
        while( totalBytesReceived < ( int32_t ) incomingPacket.remainingLength )
        {
            bytesReceived = pContext->transportInterface.recv( pContext->transportInterface.networkContext,
                                                               pContext->networkBuffer.pBuffer,
                                                               bytesToReceive );
            if( bytesReceived != bytesToReceive )
            {
                /* Partial receive occurred while trying to dump packet. */
                IotLogErrorWithArgs( "Partial receive while dumping packet."
                                     "Received bytes=%d, Expected bytes=%u",
                                     bytesReceived,
                                     bytesToReceive );
                status = MQTTRecvFailed;
                break;
            }

            /* Update number of bytes to receive. */
            totalBytesReceived += bytesReceived;
            if( ( incomingPacket.remainingLength - ( size_t ) totalBytesReceived ) < bytesToReceive )
            {
                bytesToReceive = incomingPacket.remainingLength - ( size_t ) totalBytesReceived;
            }
        }

        if( totalBytesReceived == ( int32_t ) incomingPacket.remainingLength )
        {
            IotLogInfoWithArgs( "Dumped packet. Dumped bytes=%d",
                                totalBytesReceived );
            /* Packet dumped, so no data is available. */
            status = MQTTNoDataAvailable;
        }
    }

    return status;
}

/**
 * @brief Send acks for received QoS 1/2 publishes.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] packetId, packet ID of original PUBLISH.
 * @param[in,out] pPublishState Current/updated publish state in record.
 *
 * @return MQTTSuccess or MQTTIllegalState.
 */
static MQTTStatus_t _sendPublishAcks( MQTTContext_t * const pContext,
                                      uint16_t packetId,
                                      MQTTPublishState_t * pPublishState )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;

    assert( pContext != NULL );
    assert( pPublishState != NULL );

    /* pContext->controlPacketSent doesn't seem to be part of the context.
     * Does it need to be added?
     * Additionally, need to update message timestamp if keep alive info part of
     * timestamp. */
    switch( *pPublishState )
    {
        case MQTTPubAckSend:
            /* TODO: Send PubAck. Is there a function for this? */
            //status = _sendPacket( pContext, packetId, MQTTPuback );
            //if( status == MQTTSuccess )
            newState = MQTT_UpdateStateAck( pContext,
                                            packetId,
                                            MQTTPuback,
                                            MQTT_SEND );

            if( newState != MQTTPublishDone )
            {
                status = MQTTIllegalState;
            }
            break;
        case MQTTPubRecSend:
            /* TODO: Send PubRec. Is there a function for this? */
            //status = _sendPacket( pContext, packetId, MQTTPubrec );
            //if( status == MQTTSuccess )
            newState = MQTT_UpdateStateAck( pContext,
                                            packetId,
                                            MQTTPubrec,
                                            MQTT_SEND );

            if( newState != MQTTPubRelPending )
            {
                status = MQTTIllegalState;
            }
            break;
        case MQTTPubRelSend:
            /* TODO: Send PubRel. Is there a function for this? */
            //status = _sendPacket( pContext, packetId, MQTTPubrel );
            //if( status == MQTTSuccess )
            newState = MQTT_UpdateStateAck( pContext,
                                            packetId,
                                            MQTTPubrel,
                                            MQTT_SEND );

            if( newState != MQTTPubCompPending )
            {
                status = MQTTIllegalState;
            }
            break;
        case MQTTPubCompSend:
            /* TODO: Send PubComp. Is there a function for this? */
            //status = _sendPacket( pContext, packetId, MQTTPubcomp );
            //if( status == MQTTSuccess )
            newState = MQTT_UpdateStateAck( pContext,
                                            packetId,
                                            MQTTPubcomp,
                                            MQTT_SEND );

            if( newState != MQTTPublishDone )
            {
                status = MQTTIllegalState;
            }
            break;
        default:
            /* Nothing to send. */
            break;
    }
    if( ( status == MQTTSuccess ) && ( newState != MQTTStateNull ) )
    {
        *pPublishState = newState;
    }
    return status;
}

/**
 * @brief Handle received MQTT packet.
 *
 * @param[in] pContext MQTT Connection context.
 * @param[in] pIncomingPacket Incoming packet.
 *
 * @return MQTTSuccess, MQTTIllegalState, or deserialization error.
 */
static MQTTStatus_t _handleMessage( MQTTContext_t * const pContext,
                                    MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    MQTTPubAckType_t ackType;
    MQTTPublishInfo_t publishInfo;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );

    /* Determine ack type here so next switch doesn't duplicate code. */
    switch( pIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_PUBACK:
            ackType = MQTTPuback;
            break;
        case MQTT_PACKET_TYPE_PUBREC:
            ackType = MQTTPubrec;
            break;
        case MQTT_PACKET_TYPE_PUBREL:
            ackType = MQTTPubrel;
            break;
        case MQTT_PACKET_TYPE_PUBCOMP:
            ackType = MQTTPubcomp;
            break;
        default:
            /* Not an ack. */
            break;
    }
    switch( pIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_PUBLISH:
            /* TODO: Not sure about pPacketId arg since that's already in incoming packet. */
            status = MQTT_DeserializePublish( pIncomingPacket, NULL, &publishInfo );
            IotLogInfoWithArgs( "Publish packet deserialized with result %d.",
                                status );

            if( status == MQTTSuccess )
            {
                publishRecordState = MQTT_UpdateStatePublish( pContext,
                                                              pIncomingPacket->packetIdentifier,
                                                              MQTT_RECEIVE,
                                                              publishInfo.qos );
                IotLogInfoWithArgs( "State record updated. New state=%d.",
                                    publishRecordState );

                /* Send PUBACK or PUBREC if necessary. */
                status = _sendPublishAcks( pContext,
                                           pIncomingPacket->packetIdentifier,
                                           &publishRecordState );
            }
            if( status == MQTTSuccess )
            {
                /* TODO: Should the publish info be passed instead? */
                pContext->callbacks.appCallback( pContext, pIncomingPacket );
            }
            break;
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_PUBREC:
        case MQTT_PACKET_TYPE_PUBREL:
        case MQTT_PACKET_TYPE_PUBCOMP:
            /* TODO: Not sure about pPacketId and pSessionPresent since they don't appear in API doc. */
            status = MQTT_DeserializeAck( pIncomingPacket, NULL,  NULL );
            IotLogInfoWithArgs( "Ack packet deserialized with result: %d.",
                                status );
            if( status == MQTTSuccess )
            {
                publishRecordState = MQTT_UpdateStateAck( pContext,
                                                          pIncomingPacket->packetIdentifier,
                                                          ackType,
                                                          MQTT_RECEIVE );
                IotLogInfoWithArgs( "State record updated. New state=%d.",
                                    publishRecordState );

                /* Send PUBREL or PUBCOMP if necessary. */
                status = _sendPublishAcks( pContext,
                                           pIncomingPacket->packetIdentifier,
                                           &publishRecordState );
                if( status == MQTTSuccess )
                {
                    /* TODO: There doesn't seem to be a separate callback for acks. */
                    pContext->callbacks.appCallback( pContext, pIncomingPacket );
                }
            }
        case MQTT_PACKET_TYPE_PINGRESP:
            /* TODO: should this be handled here? pContext->waitingForPingResp = false; */
        case MQTT_PACKET_TYPE_SUBACK:
            /* Give these to the app provided callback. */
            pContext->callbacks.appCallback( pContext, pIncomingPacket );
        default:
            /* Not a publish packet or ack. */
            break;
    }
    return status;
}

static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * const pContext,
                                                        const MQTTSubscribeInfo_t * const pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Validate all the parameters. */
    if( ( pContext == NULL ) || ( pSubscriptionList == NULL ) )
    {
        LogErrorWithArgs( "Argument cannot be NULL: pContext=%p, "
                          "pSubscriptionList=%p.",
                          pContext,
                          pSubscriptionList );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0UL )
    {
        LogError( "Subscription count is 0." );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( "Packet Id for subscription packet is 0." );
        status = MQTTBadParameter;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t sendPublish( const MQTTContext_t * const pContext,
                                 const MQTTPublishInfo_t * const pPublishInfo,
                                 size_t headerSize )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesSent = 0;

    assert( pContext != NULL );
    assert( pPublishInfo != NULL );
    assert( headerSize > 0 );

    /* Send header first. */
    bytesSent = sendPacket( pContext,
                            pContext->networkBuffer.pBuffer,
                            headerSize );

    if( bytesSent < 0 )
    {
        LogError( "Transport send failed for PUBLISH header." );
        status = MQTTSendFailed;
    }
    else
    {
        LogDebugWithArgs( "Sent %d bytes of PUBLISH header.",
                          bytesSent );

        /* Send Payload. */
        bytesSent = sendPacket( pContext,
                                pPublishInfo->pPayload,
                                pPublishInfo->payloadLength );

        if( bytesSent < 0 )
        {
            LogError( "Transport send failed for PUBLISH payload." );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebugWithArgs( "Sent %d bytes of PUBLISH payload.",
                              bytesSent );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start )
{
    return later - start;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receivePacket( MQTTContext_t * const pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
                                    uint32_t timeoutMs,
                                    MQTTPacketInfo_t * const incomingPacket,
                                    bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getTimeStamp = NULL;
    uint32_t entryTimeMs = 0U, remainingTimeMs = 0U, timeTakenMs = 0U;

    assert( pContext != NULL );
    assert( incomingPacket != NULL );
    assert( pContext->callbacks.getTime != NULL );

    getTimeStamp = pContext->callbacks.getTime;
    /* Get the entry time for the function. */
    entryTimeMs = getTimeStamp();

    do
    {
        /* Transport read for incoming CONNACK packet type and length.
         * MQTT_GetIncomingPacketTypeAndLength is a blocking call and it is
         * returned after a transport receive timeout, an error, or a successful
         * receive of packet type and length. */
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.networkContext,
                                                      incomingPacket );

        /* Loop until there is data to read or if the timeout has not expired. */
    } while( ( status == MQTTNoDataAvailable ) &&
             ( calculateElapsedTime( getTimeStamp(), entryTimeMs ) < timeoutMs ) );

    if( status == MQTTSuccess )
    {
        /* Time taken in this function so far. */
        timeTakenMs = calculateElapsedTime( getTimeStamp(), entryTimeMs );

        if( timeTakenMs < timeoutMs )
        {
            /* Calculate remaining time for receiving the remainder of
             * the packet. */
            remainingTimeMs = timeoutMs - timeTakenMs;
        }

        /* Reading the remainder of the packet by transport recv.
         * Attempt to read once even if the timeout has expired at this point.
         * Invoking receivePacket with remainingTime as 0 would attempt to
         * recv from network once.*/
        if( incomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
        {
            status = receivePacket( pContext,
                                    *incomingPacket,
                                    remainingTimeMs );
        }
        else
        {
            LogErrorWithArgs( "Incorrect packet type %X received while expecting"
                              " CONNACK(%X).",
                              incomingPacket->type,
                              MQTT_PACKET_TYPE_CONNACK );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Update the packet info pointer to the buffer read. */
        incomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;

        /* Deserialize CONNACK. */
        status = MQTT_DeserializeAck( &incomingPacket, NULL, pSessionPresent );
    }

    if( status != MQTTSuccess )
    {
        LogErrorWithArgs( "CONNACK recv failed with status = %u.",
                          status );
    }
    else
    {
        LogInfo( "Received MQTT CONNACK successfully from broker." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void MQTT_Init( MQTTContext_t * const pContext,
                const MQTTTransportInterface_t * const pTransportInterface,
                const MQTTApplicationCallbacks_t * const pCallbacks,
                const MQTTFixedBuffer_t * const pNetworkBuffer )
{
    ( void ) memset( pContext, 0x00, sizeof( MQTTContext_t ) );

    pContext->connectStatus = MQTTNotConnected;
    pContext->transportInterface = *pTransportInterface;
    pContext->callbacks = *pCallbacks;
    pContext->networkBuffer = *pNetworkBuffer;

    /* Zero is not a valid packet ID per MQTT spec. Start from 1. */
    pContext->nextPacketId = 1;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           uint32_t timeoutMs,
                           bool * const pSessionPresent )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { .type = ( ( uint8_t ) 0 ) };

    if( ( pContext == NULL ) || ( pConnectInfo == NULL ) )
    {
        LogErrorWithArgs( "Argument cannot be NULL: pContext=%p, "
                          "pConnectInfo=%p.",
                          pContext,
                          pConnectInfo );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT connect packet size and remaining length. */
        status = MQTT_GetConnectPacketSize( pConnectInfo,
                                            pWillInfo,
                                            &remainingLength,
                                            &packetSize );
        LogDebugWithArgs( "CONNECT packet size is %lu and remaining length is %lu.",
                          packetSize,
                          remainingLength );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializeConnect( pConnectInfo,
                                        pWillInfo,
                                        remainingLength,
                                        &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( "Transport send failed for CONNECT packet." );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebugWithArgs( "Sent %d bytes of CONNECT packet.",
                              bytesSent );
        }
    }

    /* Read CONNACK from transport layer. */
    if( status == MQTTSuccess )
    {
        status = receiveConnack( pContext,
                                 timeoutMs,
                                 &incomingPacket,
                                 pSessionPresent );
    }

    if( status == MQTTSuccess )
    {
        LogInfo( "MQTT connection established with the broker." );
        pContext->connectStatus = MQTTConnected;
    }
    else
    {
        LogErrorWithArgs( "MQTT connection failed with status = %u.",
                          status );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent = 0;

    /* Validate arguments. */
    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetSubscribePacketSize( pSubscriptionList,
                                              subscriptionCount,
                                              &remainingLength,
                                              &packetSize );
        LogDebugWithArgs( "SUBSCRIBE packet size is %lu and remaining length is %lu.",
                          packetSize,
                          remainingLength );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT SUBSCRIBE packet. */
        status = MQTT_SerializeSubscribe( pSubscriptionList,
                                          subscriptionCount,
                                          packetId,
                                          remainingLength,
                                          &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        /* Send serialized MQTT SUBSCRIBE packet to transport layer. */
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( "Transport send failed for SUBSCRIBE packet." );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebugWithArgs( "Sent %d bytes of SUBSCRIBE packet.",
                              bytesSent );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo,
                           uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL, headerSize = 0UL;
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t publishStatus = MQTTStateNull;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogErrorWithArgs( "Argument cannot be NULL: pContext=%p, "
                          "pPublishInfo=%p.",
                          pContext,
                          pPublishInfo );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogErrorWithArgs( "Packet Id is 0 for PUBLISH with QoS=%u.",
                          pPublishInfo->qos );
        status = MQTTBadParameter;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetPublishPacketSize( pPublishInfo,
                                            &remainingLength,
                                            &packetSize );
        LogDebugWithArgs( "PUBLISH packet size is %lu and remaining length is %lu.",
                          packetSize,
                          remainingLength );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializePublishHeader( pPublishInfo,
                                              packetId,
                                              remainingLength,
                                              &( pContext->networkBuffer ),
                                              &headerSize );
        LogDebugWithArgs( "Serialized PUBLISH header size is %lu.",
                          headerSize );
    }

    if( status == MQTTSuccess )
    {
        /* Reserve state for publish message. Only to be done for QoS1 or QoS2. */
        if( pPublishInfo->qos > MQTTQoS0 )
        {
            status = MQTT_ReserveState( pContext,
                                        packetId,
                                        pPublishInfo->qos );
        }
    }

    if( status == MQTTSuccess )
    {
        /* Sends the serialized publish packet over network. */
        status = sendPublish( pContext,
                              pPublishInfo,
                              headerSize );

        /* TODO. When a publish fails, the reserved state has to be cleaned
         * up. This will have to be done once an API in state machine is
         * available. */
    }

    if( status == MQTTSuccess )
    {
        /* Update state machine after PUBLISH is sent.
         * Only to be done for QoS1 or QoS2. */
        if( pPublishInfo->qos > MQTTQoS0 )
        {
            /* TODO MQTT_UpdateStatePublish will be updated to return
             * MQTTStatus_t instead of MQTTPublishState_t. Update the
             * code when that change is made. */
            publishStatus = MQTT_UpdateStatePublish( pContext,
                                                     packetId,
                                                     MQTT_SEND,
                                                     pPublishInfo->qos );

            if( publishStatus == MQTTStateNull )
            {
                LogErrorWithArgs( "Update state for publish failed with status =%u."
                                  " However PUBLISH packet is sent to the broker."
                                  " Any further handling of ACKs for the packet Id"
                                  " will fail.",
                                  publishStatus );

                /* TODO. Need to remove this update once MQTT_UpdateStatePublish is
                 * refactored with return type of MQTTStatus_t. */
                status = MQTTBadParameter;
            }
        }
    }

    if( status != MQTTSuccess )
    {
        LogErrorWithArgs( "MQTT PUBLISH failed with status=%u.",
                          status );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext )
{
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        LogError( "pContext is NULL." );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT PINGREQ. */
        status = MQTT_SerializePingreq( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        /* Send the serialized PINGREQ packet to transport layer. */
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                MQTT_PACKET_PINGREQ_SIZE );

        if( bytesSent < 0 )
        {
            LogError( "Transport send failed for PINGREQ packet." );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebugWithArgs( "Sent %d bytes of PINGREQ packet.",
                              bytesSent );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent = 0;

    /* Validate arguments. */
    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetUnsubscribePacketSize( pSubscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
        LogDebugWithArgs( "UNSUBSCRIBE packet size is %lu and remaining length is %lu.",
                          packetSize,
                          remainingLength );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT UNSUBSCRIBE packet. */
        status = MQTT_SerializeUnsubscribe( pSubscriptionList,
                                            subscriptionCount,
                                            packetId,
                                            remainingLength,
                                            &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        /* Send serialized MQTT UNSUBSCRIBE packet to transport layer. */
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( "Transport send failed for UNSUBSCRIBE packet." );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebugWithArgs( "Sent %d bytes of UNSUBSCRIBE packet.",
                              bytesSent );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext )
{
    size_t packetSize;
    int32_t bytesSent;
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( pContext == NULL )
    {
        LogError( "pContext cannot be NULL." );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT DISCONNECT packet size. */
        status = MQTT_GetDisconnectPacketSize( &packetSize );
        LogDebugWithArgs( "MQTT DISCONNECT packet size is %lu.",
                          packetSize );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize MQTT DISCONNECT packet. */
        status = MQTT_SerializeDisconnect( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( "Transport send failed for DISCONNECT packet." );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebugWithArgs( "Sent %d bytes of DISCONNECT packet.",
                              bytesSent );
        }
    }

    if( status == MQTTSuccess )
    {
        LogInfo( "Disconnected from the broker." );
        pContext->connectStatus = MQTTNotConnected;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * const pContext,
                               uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getCurrentTime = pContext->callbacks.getTime;
    uint32_t entryTime = getCurrentTime();
    MQTTPacketInfo_t incomingPacket;

    while( ( getCurrentTime() - entryTime ) < timeoutMs )
    {
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      &incomingPacket );

        if( ( status != MQTTSuccess ) && ( status != MQTTNoDataAvailable ) )
        {
            IotLogErrorWithArgs( "Receiving incoming packet length failed. Status=%d",
                                 status );
        }

        /* Receive packet. */
        if( status == MQTTSuccess )
        {
            status = _receivePacket( pContext, incomingPacket );
        }

        /* Handle received packet. */
        if( status == MQTTSuccess )
        {
            incomingPacket.pRemainingData = pContext->networkBuffer.pBuffer;
            status = _handleMessage( pContext, &incomingPacket );
        }

        if( status != MQTTSuccess && status != MQTTNoDataAvailable )
        {
            /* Error, break. */
            IotLogErrorWithArgs( "Exiting receive loop. Error status=%d",
                                 status );
            /* TODO signal connection to close? */
            break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext )
{
    uint16_t packetId = pContext->nextPacketId;

    pContext->nextPacketId++;

    if( pContext->nextPacketId == 0U )
    {
        pContext->nextPacketId = 1;
    }

    return packetId;
}

/*-----------------------------------------------------------*/
