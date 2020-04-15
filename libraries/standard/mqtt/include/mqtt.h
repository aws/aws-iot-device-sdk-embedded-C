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

#include "config.h"
#include "mqtt_lightweight.h"

struct MQTTApplicationCallbacks;
typedef struct MQTTApplicationCallbacks MQTTApplicationCallbacks_t;

struct MQTTPubAckInfo;
typedef struct MQTTPubAckInfo MQTTPubAckInfo_t;

struct MQTTContext;
typedef struct MQTTContext MQTTContext_t;

struct MQTTTransportInterface;
typedef struct MQTTTransportInterface MQTTTransportInterface_t;

typedef int32_t (* MQTTTransportSendFunc_t )( MQTTNetworkContext_t context,
                                              const void * pMessage,
                                              size_t bytesToSend );

typedef uint32_t (* MQTTGetCurrentTimeFunc_t )( void );

typedef void (* MQTTEventCallback_t )( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pPacketInfo );

typedef enum MQTTConnectionStatus
{
    MQTTNotConnected,
    MQTTConnected
} MQTTConnectionStatus_t;

typedef enum MQTTPublishState
{
    MQTTPublishSend,
    MQTTPubAckSend,
    MQTTPubRecSend,
    MQTTPubRelSend,
    MQTTPubCompSend,
    MQTTPubAckPending,
    MQTTPubRelPending,
    MQTTPubRecPending,
    MQTTPubCompPending,
    MQTTPublishDone
} MQTTPublishState_t;

typedef enum MQTTPubAckType
{
    MQTTPuback,
    MQTTPubrec,
    MQTTPubrel,
    MQTTPubcomp
} MQTTPubAckType_t;

struct MQTTTransportInterface
{
    MQTTTransportSendFunc_t send;
    MQTTTransportRecvFunc_t recv;
    MQTTNetworkContext_t networkContext;
};

struct MQTTApplicationCallbacks
{
    MQTTGetCurrentTimeFunc_t getTime;
    MQTTEventCallback_t appCallback;
};

struct MQTTPubAckInfo
{
    uint16_t packetId;
    MQTTPubAckType_t ackType;
    MQTTPublishState_t publishState;
};

struct MQTTContext
{
    MQTTPubAckInfo_t outgoingPublishRecords[ MQTT_MAX_QUEUED_PUBLISH_MESSAGES ];
    size_t outgoingPublishCount;
    MQTTPubAckInfo_t incomingPublishRecords[ MQTT_MAX_QUEUED_PUBLISH_MESSAGES ];
    size_t incomingPublishCount;

    const MQTTTransportInterface_t * pTransportInterface;
    const MQTTFixedBuffer_t * pNetworkBuffer;

    uint16_t nextPacketId;
    MQTTConnectionStatus_t connectStatus;
    const MQTTApplicationCallbacks_t * pCallbacks;
    uint32_t lastPacketTime;
};

void MQTT_Init( MQTTContext_t * const pContext,
                const MQTTTransportInterface_t * const pTransportInterface,
                const MQTTApplicationCallbacks_t * const pCallbacks,
                const MQTTFixedBuffer_t * const pNetworkBuffer );

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           bool * const pSessionPresent );

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount );

MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo );

MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext );

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount );

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext );

MQTTStatus_t MQTT_Process( MQTTContext_t * const pContext,
                           uint32_t timeoutMs );

uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext );
