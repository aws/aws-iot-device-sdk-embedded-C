#include <string.h>

#include "mqtt_lightweight.h"

#define MQTT_VERSION_3_1_1    ( ( uint8_t ) 4U )

#define MQTT_PACKET_CONNECT_MAX_SIZE    ( 327700UL )

#define MQTT_CONNECT_FLAG_CLEAN          ( 1 )
#define MQTT_CONNECT_FLAG_WILL           ( 2 )
#define MQTT_CONNECT_FLAG_WILL_QOS1      ( 3 )
#define MQTT_CONNECT_FLAG_WILL_QOS2      ( 4 )
#define MQTT_CONNECT_FLAG_WILL_RETAIN    ( 5 )
#define MQTT_CONNECT_FLAG_PASSWORD       ( 6 )
#define MQTT_CONNECT_FLAG_USERNAME       ( 7 )

#define UINT8_SET_BIT( x, position )    ( ( x ) = ( uint8_t ) ( ( x ) | ( 0x01U << ( position ) ) ) )

#define UINT16_HIGH_BYTE( x )    ( ( uint8_t ) ( ( x ) >> 8 ) )
#define UINT16_LOW_BYTE( x )     ( ( uint8_t ) ( ( x ) & 0x00ffU ) )

static size_t remainingLengthEncodedSize( size_t length )
{
    size_t encodedSize;

    /* Determine how many bytes are needed to encode length.
     * The values below are taken from the MQTT 3.1.1 spec. */

    /* 1 byte is needed to encode lengths between 0 and 127. */
    if( length < 128U )
    {
        encodedSize = 1U;
    }
    /* 2 bytes are needed to encode lengths between 128 and 16,383. */
    else if( length < 16384U )
    {
        encodedSize = 2U;
    }
    /* 3 bytes are needed to encode lengths between 16,384 and 2,097,151. */
    else if( length < 2097152U )
    {
        encodedSize = 3U;
    }
    /* 4 bytes are needed to encode lengths between 2,097,152 and 268,435,455. */
    else
    {
        encodedSize = 4U;
    }

    return encodedSize;
}

static uint8_t * encodeRemainingLength( uint8_t * pDestination,
                                        size_t length )
{
    uint8_t lengthByte;
    uint8_t * pLengthEnd = pDestination;
    size_t remainingLength = length;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        lengthByte = ( uint8_t ) ( remainingLength % 128U );
        remainingLength = remainingLength / 128U;

        /* Set the high bit of this byte, indicating that there's more data. */
        if( remainingLength > 0U )
        {
            UINT8_SET_BIT( lengthByte, 7 );
        }

        /* Output a single encoded byte. */
        *pLengthEnd = lengthByte;
        pLengthEnd++;
    } while( remainingLength > 0U );

    return pLengthEnd;
}


static uint8_t * encodeString( uint8_t * pDestination,
                               const char * source,
                               uint16_t sourceLength )
{
    uint8_t * pBuffer = pDestination;

    /* The first byte of a UTF-8 string is the high byte of the string length. */
    *pBuffer = UINT16_HIGH_BYTE( sourceLength );
    pBuffer++;

    /* The second byte of a UTF-8 string is the low byte of the string length. */
    *pBuffer = UINT16_LOW_BYTE( sourceLength );
    pBuffer++;

    /* Copy the string into pBuffer. */
    ( void ) memcpy( pBuffer, source, sourceLength );

    /* Return the pointer to the end of the encoded string. */
    pBuffer += sourceLength;

    return pBuffer;
}

MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t remainingLength;

    /* The CONNECT packet will always include a 10-byte variable header. */
    size_t connectPacketSize = 10U;

    /* Add the length of the client identifier. */
    connectPacketSize += pConnectInfo->clientIdentifierLength + sizeof( uint16_t );

    /* Add the lengths of the will message and topic name if provided. */
    if( pWillInfo != NULL )
    {
        connectPacketSize += pWillInfo->topicNameLength + sizeof( uint16_t ) +
                             pWillInfo->payloadLength + sizeof( uint16_t );
    }

    /* Add the lengths of the user naem and password if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        connectPacketSize += pConnectInfo->userNameLength + sizeof( uint16_t );
    }

    if( pConnectInfo->pPassword != NULL )
    {
        connectPacketSize += pConnectInfo->passwordLength + sizeof( uint16_t );
    }

    /* At this point, the "Remaining Length" field of the MQTT CONNECT packet has
     * been calculated. */
    remainingLength = connectPacketSize;

    /* Calculate the full size of the MQTT CONNECT packet by adding the size of
     * the "Remaining Length" field plus 1 byte for the "Packet Type" field. */
    connectPacketSize += 1U + remainingLengthEncodedSize( connectPacketSize );

    /* Check that the CONNECT packet is within the bounds of the MQTT spec. */
    if( connectPacketSize > MQTT_PACKET_CONNECT_MAX_SIZE )
    {
        status = MQTTBadParameter;
    }
    else
    {
        *pRemainingLength = remainingLength;
        *pPacketSize = connectPacketSize;
    }

    return status;
}

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    uint8_t connectFlags = 0;
    uint8_t * pIndex = pBuffer->pBuffer;

    /* The first byte in the CONNECT packet is the control packet type. */
    *pIndex = MQTT_PACKET_TYPE_CONNECT;
    pIndex++;

    /* The remaining length of the CONNECT packet is encoded starting from the
     * second byte. The remaining length does not include the length of the fixed
     * header or the encoding of the remaining length. */
    pIndex = encodeRemainingLength( pIndex, remainingLength );

    /* The string "MQTT" is placed at the beginning of the CONNECT packet's variable
     * header. This string is 4 bytes long. */
    pIndex = encodeString( pIndex, "MQTT", 4 );

    /* The MQTT protocol version is the second field of the variable header. */
    *pIndex = MQTT_VERSION_3_1_1;
    pIndex++;

    /* Set the clean session flag if needed. */
    if( pConnectInfo->cleanSession == true )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_CLEAN );
    }

    /* Set the flags for username and password if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_USERNAME );
    }

    if( pConnectInfo->pPassword != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_PASSWORD );
    }

    /* Set will flag if a Last Will and Testament is provided. */
    if( pWillInfo != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL );

        /* Flags only need to be changed for Will QoS 1 or 2. */
        if( pWillInfo->qos == MQTTQoS1 )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS1 );
        }
        else if( pWillInfo->qos == MQTTQoS2 )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS2 );
        }

        if( pWillInfo->retain == true )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_RETAIN );
        }
    }

    *pIndex = connectFlags;
    pIndex++;

    /* Write the 2 bytes of the keep alive interval into the CONNECT packet. */
    *pIndex = UINT16_HIGH_BYTE( pConnectInfo->keepAliveSeconds );
    *( pIndex + 1 ) = UINT16_LOW_BYTE( pConnectInfo->keepAliveSeconds );
    pIndex += 2;

    /* Write the client identifier into the CONNECT packet. */
    pIndex = encodeString( pIndex,
                           pConnectInfo->pClientIdentifier,
                           pConnectInfo->clientIdentifierLength );

    /* Write the will topic name and message into the CONNECT packet if provided. */
    if( pWillInfo != NULL )
    {
        pIndex = encodeString( pIndex,
                               pWillInfo->pTopicName,
                               pWillInfo->topicNameLength );
        pIndex = encodeString( pIndex,
                               pWillInfo->pPayload,
                               ( uint16_t ) pWillInfo->payloadLength );
    }

    /* Encode the user name if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pUserName, pConnectInfo->userNameLength );
    }

    /* Encode the password if provided. */
    if( pConnectInfo->pPassword != NULL )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pPassword, pConnectInfo->passwordLength );
    }

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
                                      const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        const MQTTFixedBuffer_t * const pBuffer )
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
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          const MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_GetIncomingPacket( TransportRecvFunc_t recvFunc,
                                     MQTTNetworkContext_t networkContext,
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
