#include "mqtt_lightweight.h"

#warning "Temporary workaround, remove following line"
#define MQTT_MAX_QUEUED_PUBLISH_MESSAGES 10

struct MQTTApplicationCallbacks;
typedef struct MQTTApplicationCallbacks MQTTApplicationCallbacks_t;

struct MQTTPubAckInfo;
typedef struct MQTTPubAckInfo MQTTPubAckInfo_t;

struct MQTTContext;
typedef struct MQTTContext MQTTContext_t;

struct MQTTTransportInterface;
typedef struct MQTTTransportInterface MQTTTransportInterface_t;

typedef int32_t (* TransportWriteFunc_t )( MQTTNetworkContext_t context,
                                           void * pBuffer,
                                           size_t bytesToWrite );

typedef uint32_t (* GetCurrentTimeFunc_t )( void );

typedef void (* MQTTEventCallback_t )( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pPacketInfo );

typedef enum MQTTConnectionStatus
{
    MQTTNotConnected,
    MQTTConnectionInProgress,
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
    TransportWriteFunc_t write;
    TransportReadFunc_t read;
    MQTTNetworkContext_t * networkContext;
};

struct MQTTApplicationCallbacks
{
    GetCurrentTimeFunc_t getTime;
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

    MQTTTransportInterface_t transportInterface;
    uint16_t nextPacketId;

    MQTTFixedBuffer_t txBuffer;
    MQTTFixedBuffer_t rxBuffer;

    MQTTConnectionStatus_t connectStatus;
    MQTTApplicationCallbacks_t callbacks;
    bool controlPacketSent;
};

void MQTT_Init( MQTTContext_t * const pContext,
                const MQTTTransportInterface_t * const pTransportInterface,
                const MQTTApplicationCallbacks_t * const pCallbacks,
                const MQTTFixedBuffer_t * const pTxBuffer,
                const MQTTFixedBuffer_t * const pRxBuffer );

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
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
