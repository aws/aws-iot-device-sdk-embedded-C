#include "mqtt.h"

void MQTT_Init( MQTTContext_t * const pContext,
                const MQTTTransportInterface_t * const pTransportInterface,
                const MQTTApplicationCallbacks_t * const pCallbacks,
                const MQTTFixedBuffer_t * const pTxBuffer,
                const MQTTFixedBuffer_t * const pRxBuffer )
{

}

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           bool * const pSessionPresent )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Process( MQTTContext_t * const pContext,
                           uint32_t timeoutMs )
{
    return MQTTSuccess;
}

uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext )
{
    return ( uint16_t) 1;
}
