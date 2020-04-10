#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "config.h"

struct MQTTFixedBuffer;
typedef struct MQTTFixedBuffer MQTTFixedBuffer_t;

struct MQTTConnectInfo;
typedef struct MQTTConnectInfo MQTTConnectInfo_t;

struct MQTTSubscribeInfo;
typedef struct MQTTSubscribeInfo MQTTSubscribeInfo_t;

struct MqttPublishInfo;
typedef struct MqttPublishInfo MQTTPublishInfo_t;

struct MQTTPacketInfo;
typedef struct MQTTPacketInfo MQTTPacketInfo_t;

typedef int32_t (* TransportReadFunc_t )( MQTTNetworkContext_t context,
                                          void * pBuffer,
                                          size_t bytesToRead );

typedef enum MQTTStatus
{
    MQTTSuccess = 0,
    MQTTBadParameter,
    MQTTNoMemory,
    MQTTBadResponse,
    MQTTServerRefused
} MQTTStatus_t;

typedef enum MQTTQoS
{
    MQTTQoS0 = 0,
    MQTTQoS1 = 1,
    MQTTQoS2 = 2
} MQTTQoS_t;

struct MQTTFixedBuffer
{
    uint8_t * pBuffer;
    size_t size;
};

struct MQTTConnectInfo
{
    bool cleanSession;
    uint16_t keepAliveSeconds;
    const char * pClientIdentifier;
    uint16_t clientIdentifierLength;
    const char * pUserName;
    uint16_t userNameLength;
    const char * pPassword;
    uint16_t passwordLength;
};

struct MQTTSubscribeInfo
{
    MQTTQoS_t qos;
    const char * pTopicFilter;
    uint16_t topicFilterLength;
};

struct MqttPublishInfo
{
    MQTTQoS_t qos;
    bool retain;
    const char * pTopicName;
    uint16_t topicNameLength;
    const void * pPayload;
    size_t payloadLength;
};

struct MQTTPacketInfo
{
    uint8_t type;
    uint16_t packetIdentifier;
    uint8_t * pRemainingData;
    size_t remainingLength;
};

MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    size_t remainingLength,
                                    MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SubscriptionPacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize );

MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * const pPublishInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );

MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * const pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize );

MQTTStatus_t MQTT_SerializeDisconnect( MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SerializePingreq( MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_GetPacket( TransportReadFunc_t readFunc,
                             MQTTPacketInfo_t * const pIncomingPacket );

MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo );

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent );
