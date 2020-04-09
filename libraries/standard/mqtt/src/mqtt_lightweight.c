#include "mqtt_lightweight.h"

MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    size_t remainingLength,
                                    MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SubscriptionPacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * const pPublishInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * const pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializeDisconnect( MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializePingreq( MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_GetPacket( TransportReadFunc_t readFunc,
                             MQTTPacketInfo_t * const pIncomingPacket )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent )
{
    return MQTTSuccess;
}
