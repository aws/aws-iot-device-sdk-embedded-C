/*
 * coreMQTT v1.1.0
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

/**
 * @file core_mqtt.c
 * @brief Implements the user-facing functions in core_mqtt.h.
 */

/* Standard includes. */
#include <string.h>

/* MQTT include. */
#include "core_mqtt.h"

/* Ensure that config macros, required for the library build, have been defined. */
#ifndef MQTT_STATE_ARRAY_MAX_COUNT
    #error "MQTT_STATE_ARRAY_MAX_COUNT must be defined for the MQTT library build."
#endif

#ifndef MQTT_RECV_POLLING_TIMEOUT_MS
    #define MQTT_RECV_POLLING_TIMEOUT_MS    ( 1000U )
#endif

#ifndef MQTT_SEND_RETRY_TIMEOUT_MS
    #define MQTT_SEND_RETRY_TIMEOUT_MS      ( 1000U )
#endif

#ifndef MQTT_PINGRESP_TIMEOUT_MS
    #define MQTT_PINGRESP_TIMEOUT_MS        ( 5000U )
#endif

/*-----------------------------------------------------------*/

/**
 * @brief The string representation of the CONNACK return codes.
 */
static const char * const connackReturnCodeStrings[] =
{
    "Connection accepted.",
    "Connection refused: Unacceptable protocol version.",
    "Connection refused: Identifier rejected.",
    "Connection refused: Server unavailable.",
    "Connection refused: Bad user name or password.",
    "Connection refused: Not authorized."
};

/**
 * @brief The string representation of the MQTT library status codes.
 */
static const char * const mqttStatusStrings[] =
{
    "MQTTSuccess",
    "MQTTBadParameter",
    "MQTTNoMemory",
    "MQTTRecvFailed",
    "MQTTSendFailed",
    "MQTTBadResponse",
    "MQTTServerRefused",
    "MQTTNoDataAvailable",
    "MQTTNeedMoreBytes",
    "MQTTIllegalState",
    "MQTTStateCollision",
    "MQTTKeepAliveTimeout"
};

/*-----------------------------------------------------------*/

const char * MQTT_Status_strerror( MQTTStatus_t status )
{
    const char * pMessage = NULL;

    if( status >= 0 )
    {
        pMessage = mqttStatusStrings[ status ];
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

const char * MQTT_Connect_strerror( MQTTConnectStatus_t status )
{
    const char * pMessage = NULL;

    if( status >= 0 )
    {
        pMessage = connackReturnCodeStrings[ status ];
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

static void handleKeepAlive( MQTTContext_t * pContext )
{
    uint32_t now = 0U, keepAliveMs = 0U, elapsedTime = 0U;
    MQTTStatus_t status = MQTTSuccess;

    assert( pContext != NULL );

    now = pContext->getTime();
    keepAliveMs = ( uint32_t ) ( pContext->connectInfo.keepAliveSeconds * 1000U );

    /* Check if the keep-alive interval has expired. */
    if( ( now - pContext->lastPacketTime ) > keepAliveMs )
    {
        /* Update the last packet time to the current time. */
        pContext->lastPacketTime = now;

        /* Send a PINGREQ to the server. */
        status = MQTT_Ping( pContext );

        if( status == MQTTSuccess )
        {
            /* Update the time at which the PINGREQ was sent. */
            pContext->pingReqSendTimeMs = now;
        }
    }
    else
    {
        /* Calculate the elapsed time since the last packet was sent or received. */
        elapsedTime = now - pContext->lastPacketTime;

        /* Check if the elapsed time is greater than the keep-alive interval. */
        if( elapsedTime > keepAliveMs )
        {
            /* Update the last packet time to the current time. */
            pContext->lastPacketTime = now;

            /* Send a PINGREQ to the server. */
            status = MQTT_Ping( pContext );

            if( status == MQTTSuccess )
            {
                /* Update the time at which the PINGREQ was sent. */
                pContext->pingReqSendTimeMs = now;
            }
        }
    }
}

/*-----------------------------------------------------------*/

static MQTTStatus_t receivePacket( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { 0 };
    size_t bytesReceived = 0U;

    assert( pContext != NULL );

    /* Receive the incoming packet. */
    status = pContext->transportInterface.recv( pContext->transportInterface.pNetworkContext,
                                                pContext->networkBuffer.pBuffer,
                                                pContext->networkBuffer.size );

    if( status == MQTTSuccess )
    {
        /* Parse the incoming packet. */
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->networkBuffer.pBuffer,
                                                      pContext->networkBuffer.size,
                                                      &incomingPacket );

        if( status == MQTTSuccess )
        {
            /* Process the incoming packet. */
            status = MQTT_ProcessIncomingPacket( pContext, &incomingPacket );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t now = 0U, keepAliveMs = 0U, elapsedTime = 0U;

    assert( pContext != NULL );

    /* Get the current time. */
    now = pContext->getTime();

    /* Calculate the keep-alive interval in milliseconds. */
    keepAliveMs = ( uint32_t ) ( pContext->connectInfo.keepAliveSeconds * 1000U );

    /* Check if the keep-alive interval has expired. */
    if( ( now - pContext->lastPacketTime ) > keepAliveMs )
    {
        /* Update the last packet time to the current time. */
        pContext->lastPacketTime = now;

        /* Send a PINGREQ to the server. */
        status = MQTT_Ping( pContext );

        if( status == MQTTSuccess )
        {
            /* Update the time at which the PINGREQ was sent. */
            pContext->pingReqSendTimeMs = now;
        }
    }
    else
    {
        /* Calculate the elapsed time since the last packet was sent or received. */
        elapsedTime = now - pContext->lastPacketTime;

        /* Check if the elapsed time is greater than the keep-alive interval. */
        if( elapsedTime > keepAliveMs )
        {
            /* Update the last packet time to the current time. */
            pContext->lastPacketTime = now;

            /* Send a PINGREQ to the server. */
            status = MQTT_Ping( pContext );

            if( status == MQTTSuccess )
            {
                /* Update the time at which the PINGREQ was sent. */
                pContext->pingReqSendTimeMs = now;
            }
        }
    }

    /* Receive and process incoming packets. */
    if( status == MQTTSuccess )
    {
        status = receivePacket( pContext );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t pingreq = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to PINGREQ. */
    pingreq.type = MQTT_PACKET_TYPE_PINGREQ;

    /* Send the PINGREQ packet. */
    status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                pingreq.pRemainingData,
                                                pingreq.remainingLength );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t connectPacket = { 0 };

    assert( pContext != NULL );
    assert( pConnectInfo != NULL );
    assert( pSessionPresent != NULL );

    /* Set the packet type to CONNECT. */
    connectPacket.type = MQTT_PACKET_TYPE_CONNECT;

    /* Set the remaining length of the packet. */
    connectPacket.remainingLength = MQTT_GetConnectPacketSize( pConnectInfo, pWillInfo );

    /* Serialize the CONNECT packet. */
    status = MQTT_SerializeConnect( pContext->networkBuffer.pBuffer,
                                    pContext->networkBuffer.size,
                                    pConnectInfo,
                                    pWillInfo,
                                    &connectPacket );

    if( status == MQTTSuccess )
    {
        /* Send the CONNECT packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    connectPacket.remainingLength );

        if( status == MQTTSuccess )
        {
            /* Receive the CONNACK packet. */
            status = receivePacket( pContext );

            if( status == MQTTSuccess )
            {
                /* Check if the session is present. */
                *pSessionPresent = ( pContext->connectInfo.cleanSession == 0U ) ? true : false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t disconnectPacket = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to DISCONNECT. */
    disconnectPacket.type = MQTT_PACKET_TYPE_DISCONNECT;

    /* Send the DISCONNECT packet. */
    status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                disconnectPacket.pRemainingData,
                                                disconnectPacket.remainingLength );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t subscribePacket = { 0 };

    assert( pContext != NULL );
    assert( pSubscriptionList != NULL );
    assert( subscriptionCount > 0U );

    /* Set the packet type to SUBSCRIBE. */
    subscribePacket.type = MQTT_PACKET_TYPE_SUBSCRIBE;

    /* Set the remaining length of the packet. */
    subscribePacket.remainingLength = MQTT_GetSubscribePacketSize( pSubscriptionList, subscriptionCount );

    /* Serialize the SUBSCRIBE packet. */
    status = MQTT_SerializeSubscribe( pContext->networkBuffer.pBuffer,
                                      pContext->networkBuffer.size,
                                      pSubscriptionList,
                                      subscriptionCount,
                                      packetId,
                                      &subscribePacket );

    if( status == MQTTSuccess )
    {
        /* Send the SUBSCRIBE packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    subscribePacket.remainingLength );

        if( status == MQTTSuccess )
        {
            /* Receive the SUBACK packet. */
            status = receivePacket( pContext );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t unsubscribePacket = { 0 };

    assert( pContext != NULL );
    assert( pSubscriptionList != NULL );
    assert( subscriptionCount > 0U );

    /* Set the packet type to UNSUBSCRIBE. */
    unsubscribePacket.type = MQTT_PACKET_TYPE_UNSUBSCRIBE;

    /* Set the remaining length of the packet. */
    unsubscribePacket.remainingLength = MQTT_GetUnsubscribePacketSize( pSubscriptionList, subscriptionCount );

    /* Serialize the UNSUBSCRIBE packet. */
    status = MQTT_SerializeUnsubscribe( pContext->networkBuffer.pBuffer,
                                        pContext->networkBuffer.size,
                                        pSubscriptionList,
                                        subscriptionCount,
                                        packetId,
                                        &unsubscribePacket );

    if( status == MQTTSuccess )
    {
        /* Send the UNSUBSCRIBE packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    unsubscribePacket.remainingLength );

        if( status == MQTTSuccess )
        {
            /* Receive the UNSUBACK packet. */
            status = receivePacket( pContext );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t publishPacket = { 0 };

    assert( pContext != NULL );
    assert( pPublishInfo != NULL );

    /* Set the packet type to PUBLISH. */
    publishPacket.type = MQTT_PACKET_TYPE_PUBLISH;

    /* Set the remaining length of the packet. */
    publishPacket.remainingLength = MQTT_GetPublishPacketSize( pPublishInfo );

    /* Serialize the PUBLISH packet. */
    status = MQTT_SerializePublish( pContext->networkBuffer.pBuffer,
                                    pContext->networkBuffer.size,
                                    pPublishInfo,
                                    packetId,
                                    &publishPacket );

    if( status == MQTTSuccess )
    {
        /* Send the PUBLISH packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    publishPacket.remainingLength );

        if( status == MQTTSuccess )
        {
            /* Receive the PUBACK packet. */
            status = receivePacket( pContext );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_PubAck( MQTTContext_t * pContext,
                          uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t pubackPacket = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to PUBACK. */
    pubackPacket.type = MQTT_PACKET_TYPE_PUBACK;

    /* Serialize the PUBACK packet. */
    status = MQTT_SerializePubAck( pContext->networkBuffer.pBuffer,
                                   pContext->networkBuffer.size,
                                   packetId,
                                   &pubackPacket );

    if( status == MQTTSuccess )
    {
        /* Send the PUBACK packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    pubackPacket.remainingLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_PubRec( MQTTContext_t * pContext,
                          uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t pubrecPacket = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to PUBREC. */
    pubrecPacket.type = MQTT_PACKET_TYPE_PUBREC;

    /* Serialize the PUBREC packet. */
    status = MQTT_SerializePubRec( pContext->networkBuffer.pBuffer,
                                   pContext->networkBuffer.size,
                                   packetId,
                                   &pubrecPacket );

    if( status == MQTTSuccess )
    {
        /* Send the PUBREC packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    pubrecPacket.remainingLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_PubRel( MQTTContext_t * pContext,
                          uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t pubrelPacket = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to PUBREL. */
    pubrelPacket.type = MQTT_PACKET_TYPE_PUBREL;

    /* Serialize the PUBREL packet. */
    status = MQTT_SerializePubRel( pContext->networkBuffer.pBuffer,
                                   pContext->networkBuffer.size,
                                   packetId,
                                   &pubrelPacket );

    if( status == MQTTSuccess )
    {
        /* Send the PUBREL packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    pubrelPacket.remainingLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_PubComp( MQTTContext_t * pContext,
                           uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t pubcompPacket = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to PUBCOMP. */
    pubcompPacket.type = MQTT_PACKET_TYPE_PUBCOMP;

    /* Serialize the PUBCOMP packet. */
    status = MQTT_SerializePubComp( pContext->networkBuffer.pBuffer,
                                    pContext->networkBuffer.size,
                                    packetId,
                                    &pubcompPacket );

    if( status == MQTTSuccess )
    {
        /* Send the PUBCOMP packet. */
        status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                    pContext->networkBuffer.pBuffer,
                                                    pubcompPacket.remainingLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_PingResp( MQTTContext_t * pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t pingrespPacket = { 0 };

    assert( pContext != NULL );

    /* Set the packet type to PINGRESP. */
    pingrespPacket.type = MQTT_PACKET_TYPE_PINGRESP;

    /* Send the PINGRESP packet. */
    status = pContext->transportInterface.send( pContext->transportInterface.pNetworkContext,
                                                pingrespPacket.pRemainingData,
                                                pingrespPacket.remainingLength );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( const uint8_t * pBuffer,
                                                  size_t bufferSize,
                                                  MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the fixed header of the incoming packet. */
    status = MQTT_DeserializeFixedHeader( pBuffer, bufferSize, pIncomingPacket );

    if( status == MQTTSuccess )
    {
        /* Parse the remaining length of the incoming packet. */
        status = MQTT_DeserializeRemainingLength( pBuffer, bufferSize, pIncomingPacket );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ProcessIncomingPacket( MQTTContext_t * pContext,
                                         const MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );

    /* Process the incoming packet based on its type. */
    switch( pIncomingPacket->type )
    {
        case MQTT_PACKET_TYPE_CONNACK:
            status = MQTT_DeserializeConnack( pContext->networkBuffer.pBuffer,
                                              pContext->networkBuffer.size,
                                              pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_PUBLISH:
            status = MQTT_DeserializePublish( pContext->networkBuffer.pBuffer,
                                              pContext->networkBuffer.size,
                                              pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_PUBACK:
            status = MQTT_DeserializePubAck( pContext->networkBuffer.pBuffer,
                                             pContext->networkBuffer.size,
                                             pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_PUBREC:
            status = MQTT_DeserializePubRec( pContext->networkBuffer.pBuffer,
                                             pContext->networkBuffer.size,
                                             pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_PUBREL:
            status = MQTT_DeserializePubRel( pContext->networkBuffer.pBuffer,
                                             pContext->networkBuffer.size,
                                             pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_PUBCOMP:
            status = MQTT_DeserializePubComp( pContext->networkBuffer.pBuffer,
                                              pContext->networkBuffer.size,
                                              pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_SUBACK:
            status = MQTT_DeserializeSubAck( pContext->networkBuffer.pBuffer,
                                             pContext->networkBuffer.size,
                                             pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_UNSUBACK:
            status = MQTT_DeserializeUnsubAck( pContext->networkBuffer.pBuffer,
                                               pContext->networkBuffer.size,
                                               pIncomingPacket );
            break;

        case MQTT_PACKET_TYPE_PINGRESP:
            status = MQTT_DeserializePingResp( pContext->networkBuffer.pBuffer,
                                               pContext->networkBuffer.size,
                                               pIncomingPacket );
            break;

        default:
            status = MQTTBadResponse;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeConnect( uint8_t * pBuffer,
                                    size_t bufferSize,
                                    const MQTTConnectInfo_t * pConnectInfo,
                                    const MQTTPublishInfo_t * pWillInfo,
                                    MQTTPacketInfo_t * pConnectPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pConnectInfo != NULL );
    assert( pConnectPacket != NULL );

    /* Serialize the fixed header of the CONNECT packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pConnectPacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the CONNECT packet. */
        status = MQTT_SerializeConnectVariableHeader( pBuffer, bufferSize, pConnectInfo, pWillInfo );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize the payload of the CONNECT packet. */
        status = MQTT_SerializeConnectPayload( pBuffer, bufferSize, pConnectInfo, pWillInfo );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePublish( uint8_t * pBuffer,
                                    size_t bufferSize,
                                    const MQTTPublishInfo_t * pPublishInfo,
                                    uint16_t packetId,
                                    MQTTPacketInfo_t * pPublishPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pPublishInfo != NULL );
    assert( pPublishPacket != NULL );

    /* Serialize the fixed header of the PUBLISH packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pPublishPacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the PUBLISH packet. */
        status = MQTT_SerializePublishVariableHeader( pBuffer, bufferSize, pPublishInfo, packetId );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize the payload of the PUBLISH packet. */
        status = MQTT_SerializePublishPayload( pBuffer, bufferSize, pPublishInfo );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePubAck( uint8_t * pBuffer,
                                   size_t bufferSize,
                                   uint16_t packetId,
                                   MQTTPacketInfo_t * pPubAckPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pPubAckPacket != NULL );

    /* Serialize the fixed header of the PUBACK packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pPubAckPacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the PUBACK packet. */
        status = MQTT_SerializePubAckVariableHeader( pBuffer, bufferSize, packetId );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePubRec( uint8_t * pBuffer,
                                   size_t bufferSize,
                                   uint16_t packetId,
                                   MQTTPacketInfo_t * pPubRecPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pPubRecPacket != NULL );

    /* Serialize the fixed header of the PUBREC packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pPubRecPacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the PUBREC packet. */
        status = MQTT_SerializePubRecVariableHeader( pBuffer, bufferSize, packetId );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePubRel( uint8_t * pBuffer,
                                   size_t bufferSize,
                                   uint16_t packetId,
                                   MQTTPacketInfo_t * pPubRelPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pPubRelPacket != NULL );

    /* Serialize the fixed header of the PUBREL packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pPubRelPacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the PUBREL packet. */
        status = MQTT_SerializePubRelVariableHeader( pBuffer, bufferSize, packetId );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePubComp( uint8_t * pBuffer,
                                    size_t bufferSize,
                                    uint16_t packetId,
                                    MQTTPacketInfo_t * pPubCompPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pPubCompPacket != NULL );

    /* Serialize the fixed header of the PUBCOMP packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pPubCompPacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the PUBCOMP packet. */
        status = MQTT_SerializePubCompVariableHeader( pBuffer, bufferSize, packetId );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeSubscribe( uint8_t * pBuffer,
                                      size_t bufferSize,
                                      const MQTTSubscribeInfo_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      MQTTPacketInfo_t * pSubscribePacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pSubscriptionList != NULL );
    assert( pSubscribePacket != NULL );

    /* Serialize the fixed header of the SUBSCRIBE packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pSubscribePacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the SUBSCRIBE packet. */
        status = MQTT_SerializeSubscribeVariableHeader( pBuffer, bufferSize, packetId );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize the payload of the SUBSCRIBE packet. */
        status = MQTT_SerializeSubscribePayload( pBuffer, bufferSize, pSubscriptionList, subscriptionCount );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeUnsubscribe( uint8_t * pBuffer,
                                        size_t bufferSize,
                                        const MQTTSubscribeInfo_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        MQTTPacketInfo_t * pUnsubscribePacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pSubscriptionList != NULL );
    assert( pUnsubscribePacket != NULL );

    /* Serialize the fixed header of the UNSUBSCRIBE packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pUnsubscribePacket );

    if( status == MQTTSuccess )
    {
        /* Serialize the variable header of the UNSUBSCRIBE packet. */
        status = MQTT_SerializeUnsubscribeVariableHeader( pBuffer, bufferSize, packetId );
    }

    if( status == MQTTSuccess )
    {
        /* Serialize the payload of the UNSUBSCRIBE packet. */
        status = MQTT_SerializeUnsubscribePayload( pBuffer, bufferSize, pSubscriptionList, subscriptionCount );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePingReq( uint8_t * pBuffer,
                                    size_t bufferSize,
                                    MQTTPacketInfo_t * pPingReqPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pPingReqPacket != NULL );

    /* Serialize the fixed header of the PINGREQ packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pPingReqPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeDisconnect( uint8_t * pBuffer,
                                       size_t bufferSize,
                                       MQTTPacketInfo_t * pDisconnectPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pDisconnectPacket != NULL );

    /* Serialize the fixed header of the DISCONNECT packet. */
    status = MQTT_SerializeFixedHeader( pBuffer, bufferSize, pDisconnectPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeFixedHeader( const uint8_t * pBuffer,
                                          size_t bufferSize,
                                          MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the fixed header of the incoming packet. */
    status = MQTT_GetFixedHeader( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeRemainingLength( const uint8_t * pBuffer,
                                              size_t bufferSize,
                                              MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the remaining length of the incoming packet. */
    status = MQTT_GetRemainingLength( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeConnack( const uint8_t * pBuffer,
                                      size_t bufferSize,
                                      MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the CONNACK packet. */
    status = MQTT_GetConnack( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePublish( const uint8_t * pBuffer,
                                      size_t bufferSize,
                                      MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBLISH packet. */
    status = MQTT_GetPublish( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePubAck( const uint8_t * pBuffer,
                                     size_t bufferSize,
                                     MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBACK packet. */
    status = MQTT_GetPubAck( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePubRec( const uint8_t * pBuffer,
                                     size_t bufferSize,
                                     MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBREC packet. */
    status = MQTT_GetPubRec( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePubRel( const uint8_t * pBuffer,
                                     size_t bufferSize,
                                     MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBREL packet. */
    status = MQTT_GetPubRel( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePubComp( const uint8_t * pBuffer,
                                      size_t bufferSize,
                                      MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBCOMP packet. */
    status = MQTT_GetPubComp( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeSubAck( const uint8_t * pBuffer,
                                     size_t bufferSize,
                                     MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the SUBACK packet. */
    status = MQTT_GetSubAck( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeUnsubAck( const uint8_t * pBuffer,
                                       size_t bufferSize,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the UNSUBACK packet. */
    status = MQTT_GetUnsubAck( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePingResp( const uint8_t * pBuffer,
                                       size_t bufferSize,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PINGRESP packet. */
    status = MQTT_GetPingResp( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetFixedHeader( const uint8_t * pBuffer,
                                  size_t bufferSize,
                                  MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the fixed header of the incoming packet. */
    status = MQTT_ParseFixedHeader( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetRemainingLength( const uint8_t * pBuffer,
                                      size_t bufferSize,
                                      MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the remaining length of the incoming packet. */
    status = MQTT_ParseRemainingLength( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetConnack( const uint8_t * pBuffer,
                              size_t bufferSize,
                              MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the CONNACK packet. */
    status = MQTT_ParseConnack( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPublish( const uint8_t * pBuffer,
                              size_t bufferSize,
                              MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBLISH packet. */
    status = MQTT_ParsePublish( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPubAck( const uint8_t * pBuffer,
                             size_t bufferSize,
                             MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBACK packet. */
    status = MQTT_ParsePubAck( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPubRec( const uint8_t * pBuffer,
                             size_t bufferSize,
                             MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBREC packet. */
    status = MQTT_ParsePubRec( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPubRel( const uint8_t * pBuffer,
                             size_t bufferSize,
                             MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBREL packet. */
    status = MQTT_ParsePubRel( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPubComp( const uint8_t * pBuffer,
                              size_t bufferSize,
                              MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBCOMP packet. */
    status = MQTT_ParsePubComp( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetSubAck( const uint8_t * pBuffer,
                             size_t bufferSize,
                             MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the SUBACK packet. */
    status = MQTT_ParseSubAck( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetUnsubAck( const uint8_t * pBuffer,
                               size_t bufferSize,
                               MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the UNSUBACK packet. */
    status = MQTT_ParseUnsubAck( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPingResp( const uint8_t * pBuffer,
                               size_t bufferSize,
                               MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PINGRESP packet. */
    status = MQTT_ParsePingResp( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ParseFixedHeader( const uint8_t * pBuffer,
                                    size_t bufferSize,
                                    MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the fixed header of the incoming packet. */
    status = MQTT_DeserializeFixedHeader( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ParseRemainingLength( const uint8_t * pBuffer,
                                        size_t bufferSize,
                                        MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the remaining length of the incoming packet. */
    status = MQTT_DeserializeRemainingLength( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ParseConnack( const uint8_t * pBuffer,
                                size_t bufferSize,
                                MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the CONNACK packet. */
    status = MQTT_DeserializeConnack( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ParsePublish( const uint8_t * pBuffer,
                                size_t bufferSize,
                                MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBLISH packet. */
    status = MQTT_DeserializePublish( pBuffer, bufferSize, pIncomingPacket );

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ParsePubAck( const uint8_t * pBuffer,
                               size_t bufferSize,
                               MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pBuffer != NULL );
    assert( pIncomingPacket != NULL );

    /* Parse the PUBACK packet
