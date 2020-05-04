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

#include "mqtt_lightweight.h"
#include "private/mqtt_internal.h"

/**
 * @brief MQTT protocol version 3.1.1.
 */
#define MQTT_VERSION_3_1_1    ( ( uint8_t ) 4U )

/**
 * @brief Size of the fixed and variable header of a CONNECT packet.
 */
#define MQTT_PACKET_CONNECT_HEADER_SIZE    ( 10UL )

/**
 * @brief Maximum size of an MQTT CONNECT packet, per MQTT spec.
 */
#define MQTT_PACKET_CONNECT_MAX_SIZE       ( 327700UL )

/* MQTT CONNECT flags. */
#define MQTT_CONNECT_FLAG_CLEAN          ( 1 )    /**< @brief Clean session. */
#define MQTT_CONNECT_FLAG_WILL           ( 2 )    /**< @brief Will present. */
#define MQTT_CONNECT_FLAG_WILL_QOS1      ( 3 )    /**< @brief Will QoS 1. */
#define MQTT_CONNECT_FLAG_WILL_QOS2      ( 4 )    /**< @brief Will QoS 2. */
#define MQTT_CONNECT_FLAG_WILL_RETAIN    ( 5 )    /**< @brief Will retain. */
#define MQTT_CONNECT_FLAG_PASSWORD       ( 6 )    /**< @brief Password present. */
#define MQTT_CONNECT_FLAG_USERNAME       ( 7 )    /**< @brief User name present. */

/*
 * Positions of each flag in the first byte of an MQTT PUBLISH packet's
 * fixed header.
 */
#define MQTT_PUBLISH_FLAG_RETAIN         ( 0 )             /**< @brief Message retain flag. */
#define MQTT_PUBLISH_FLAG_QOS1           ( 1 )             /**< @brief Publish QoS 1. */
#define MQTT_PUBLISH_FLAG_QOS2           ( 2 )             /**< @brief Publish QoS 2. */
#define MQTT_PUBLISH_FLAG_DUP            ( 3 )             /**< @brief Duplicate message. */

/**
 * @brief The size of MQTT DISCONNECT packets, per MQTT spec.
 */
#define MQTT_DISCONNECT_PACKET_SIZE         ( 2UL )

/**
 * @brief The Remaining Length field of MQTT disconnect packets, per MQTT spec.
 */
#define MQTT_DISCONNECT_REMAINING_LENGTH    ( ( uint8_t ) 0 )

/*
 * Constants relating to CONNACK packets, defined by MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_CONNACK_REMAINING_LENGTH        ( ( uint8_t ) 2U )    /**< @brief A CONNACK packet always has a "Remaining length" of 2. */
#define MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK    ( ( uint8_t ) 0x01U ) /**< @brief The "Session Present" bit is always the lowest bit. */

/*
 * UNSUBACK, PUBACK, PUBREC, PUBREL, and PUBCOMP always have a remaining length
 * of 2.
 */
#define MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH     ( ( uint8_t ) 2 )   /**< @brief PUBACK, PUBREC, PUBREl, PUBCOMP, UNSUBACK Remaining length. */
#define MQTT_PACKET_PINGRESP_REMAINING_LENGTH       ( 0U ) /**< @brief A PINGRESP packet always has a "Remaining length" of 0. */

/**
 * @brief Set a bit in an 8-bit unsigned integer.
 */
#define UINT8_SET_BIT( x, position )    ( ( x ) = ( uint8_t ) ( ( x ) | ( 0x01U << ( position ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 1-byte unsigned int.
 *
 * @param[in] x The unsigned int to check.
 * @param[in] position Which bit to check.
 */
#define UINT8_CHECK_BIT( x, position )    ( ( ( x ) & ( 0x01U << ( position ) ) ) == ( 0x01U << ( position ) ) )

/**
 * @brief Get the high byte of a 16-bit unsigned integer.
 */
#define UINT16_HIGH_BYTE( x )    ( ( uint8_t ) ( ( x ) >> 8 ) )

/**
 * @brief Get the low byte of a 16-bit unsigned integer.
 */
#define UINT16_LOW_BYTE( x )     ( ( uint8_t ) ( ( x ) & 0x00ffU ) )

/**
 * @brief Macro for decoding a 2-byte unsigned int from a sequence of bytes.
 *
 * @param[in] ptr A uint8_t* that points to the high byte.
 */
#define UINT16_DECODE( ptr )                                \
    ( uint16_t ) ( ( ( ( uint16_t ) ( *( ptr ) ) ) << 8 ) | \
                   ( ( uint16_t ) ( *( ( ptr ) + 1 ) ) ) )

/**
 * @brief A value that represents an invalid remaining length.
 *
 * This value is greater than what is allowed by the MQTT specification.
 */
#define MQTT_REMAINING_LENGTH_INVALID               ( ( size_t ) 268435456 )

/**
 * @brief The minimum remaining length for a QoS 0 PUBLISH.
 *
 * Includes two bytes for topic name length and one byte for topic name.
 */
#define MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0      ( 3U )

/*-----------------------------------------------------------*/

static size_t _remainingLengthEncodedSize( size_t length )
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

/*-----------------------------------------------------------*/

static uint8_t * _encodeRemainingLength( uint8_t * pDestination,
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

/*-----------------------------------------------------------*/

static uint8_t * _encodeString( uint8_t * pDestination,
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

/*-----------------------------------------------------------*/

static int32_t recvExact( MQTTTransportRecvFunc_t recvFunc,
                          MQTTNetworkContext_t networkContext,
                          void * pBuffer,
                          size_t bytesToRecv )
{
    uint8_t * pIndex = pBuffer;
    size_t bytesRemaining = bytesToRecv;
    int32_t totalBytesRecvd = 0, bytesRecvd;

    while( bytesRemaining > 0 )
    {
        bytesRecvd = recvFunc( networkContext, pIndex, bytesRemaining );

        if( bytesRecvd > 0 )
        {
            bytesRemaining -= ( size_t ) bytesRecvd;
            totalBytesRecvd += ( int32_t ) bytesRecvd;
            pIndex += bytesRecvd;
        }
        else
        {
            totalBytesRecvd = -1;
            break;
        }
    }

    return totalBytesRecvd;
}

/*-----------------------------------------------------------*/

static size_t _getRemainingLength( MQTTTransportRecvFunc_t recvFunc,
                                   MQTTNetworkContext_t networkContext )
{
    size_t remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;
    uint8_t encodedByte = 0;
    int32_t bytesReceived = 0;

    /* This algorithm is copied from the MQTT v3.1.1 spec. */
    do
    {
        if( multiplier > 2097152U ) /* 128 ^ 3 */
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
        else
        {
            bytesReceived = recvFunc( networkContext, &encodedByte, 1U );
            if( bytesReceived == 1 )
            {
                remainingLength += ( ( size_t ) encodedByte & 0x7FU ) * multiplier;
                multiplier *= 128U;
                bytesDecoded++;
            }
            else
            {
                remainingLength = MQTT_REMAINING_LENGTH_INVALID;
            }
        }
        if( remainingLength == MQTT_REMAINING_LENGTH_INVALID )
        {
            break;
        }
    } while ( ( encodedByte & 0x80U ) != 0U );

    /* Check that the decoded remaining length conforms to the MQTT specification. */
    if( remainingLength != MQTT_REMAINING_LENGTH_INVALID )
    {
        expectedSize = _remainingLengthEncodedSize( remainingLength );
        if( bytesDecoded != expectedSize )
        {
            remainingLength = MQTT_REMAINING_LENGTH_INVALID;
        }
    }

    return remainingLength;
}

/*-----------------------------------------------------------*/

static bool _incomingPacketValid( uint8_t packetType )
{
    bool status = false;

    /* Check packet type. Mask out lower bits to ignore flags. */
    switch( packetType & 0xF0U )
    {
        /* Valid incoming packet types. */
        case MQTT_PACKET_TYPE_CONNACK:
        case MQTT_PACKET_TYPE_PUBLISH:
        case MQTT_PACKET_TYPE_PUBACK:
        case MQTT_PACKET_TYPE_PUBREC:
        case MQTT_PACKET_TYPE_PUBCOMP:
        case MQTT_PACKET_TYPE_SUBACK:
        case MQTT_PACKET_TYPE_UNSUBACK:
        case MQTT_PACKET_TYPE_PINGRESP:
            status = true;
            break;

        /* Any other packet type is invalid. */
        default:
            break;
    }

    /* The second bit of a PUBREL must be set, so the above switch won't handle it. */
    if( packetType == MQTT_PACKET_TYPE_PUBREL )
    {
        status = true;
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _checkPublishRemainingLength( size_t remainingLength,
                                                  MQTTQoS_t qos,
                                                  size_t qos0Minimum )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Sanity checks for "Remaining length". */
    if( qos == MQTTQoS0 )
    {
        /* Check that the "Remaining length" is greater than the minimum. */
        if( remainingLength < qos0Minimum )
        {
            IotLogDebugWithArgs( "QoS 0 PUBLISH cannot have a remaining length less than %lu.",
                                 qos0Minimum );

            status = MQTTBadResponse;
        }
    }
    else
    {
        /* Check that the "Remaining length" is greater than the minimum. For
         * QoS 1 or 2, this will be two bytes greater than for QoS 0 due to the
         * packet identifier. */
        if( remainingLength < ( qos0Minimum + 2U ) )
        {
            IotLogDebugWithArgs( "QoS 1 or 2 PUBLISH cannot have a remaining length less than %lu.",
                                 qos0Minimum + 2U );

            status = MQTTBadResponse;
        }
    }
    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _processPublishFlags( uint8_t publishFlags, MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pPublishInfo != NULL );

    /* Check for QoS 2. */
    if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 ) )
    {
        /* PUBLISH packet is invalid if both QoS 1 and QoS 2 bits are set. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) )
        {
            IotLogDebug( "Bad QoS: 3." );

            status = MQTTBadResponse;
        }
        else
        {
            pPublishInfo->qos = MQTTQoS2;
        }
    }
    /* Check for QoS 1. */
    else if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) )
    {
        pPublishInfo->qos = MQTTQoS1;
    }
    /* If the PUBLISH isn't QoS 1 or 2, then it's QoS 0. */
    else
    {
        pPublishInfo->qos = MQTTQoS0;
    }

    if( status == MQTTSuccess )
    {
        IotLogDebugWithArgs( "QoS is %d.", pPublishInfo->qos );

        /* Parse the Retain bit. */
        pPublishInfo->retain = UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );

        IotLogDebugWithArgs( "Retain bit is %d.", pPublishInfo->retain );

        /* Parse the DUP bit. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP ) )
        {
            IotLogDebug( "DUP is 1." );
        }
        else
        {
            IotLogDebug( "DUP is 0." );
        }
    }
    return status;
}

/*-----------------------------------------------------------*/

static void _logConnackResponse( uint8_t responseCode )
{
    assert( responseCode <= 5 );
    /* Declare the CONNACK response code strings. The fourth byte of CONNACK
     * indexes into this array for the corresponding response. */
    #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
        static const char * const pConnackResponses[ 6 ] =
        {
            "Connection accepted.",                               /* 0 */
            "Connection refused: unacceptable protocol version.", /* 1 */
            "Connection refused: identifier rejected.",           /* 2 */
            "Connection refused: server unavailable",             /* 3 */
            "Connection refused: bad user name or password.",     /* 4 */
            "Connection refused: not authorized."                 /* 5 */
        };
        IotLogErrorWithArgs( "%s", pConnackResponses[ responseCode ] );
    #endif
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                         bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pConnack != NULL );
    assert( pSessionPresent != NULL );
    const uint8_t * pRemainingData = pConnack->pRemainingData;

    /* According to MQTT 3.1.1, the second byte of CONNACK must specify a
     * "Remaining length" of 2. */
    if( pConnack->remainingLength != MQTT_PACKET_CONNACK_REMAINING_LENGTH )
    {
        IotLogErrorWithArgs( "CONNACK does not have remaining length of %d.",
                             MQTT_PACKET_CONNACK_REMAINING_LENGTH );

        status = MQTTBadResponse;
    }

    /* Check the reserved bits in CONNACK. The high 7 bits of the second byte
     * in CONNACK must be 0. */
    else if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
    {
        IotLogError( "Reserved bits in CONNACK incorrect." );

        status = MQTTBadResponse;
    }
    else
    {
        /* Determine if the "Session Present" bit is set. This is the lowest bit of
         * the second byte in CONNACK. */
        if( ( pRemainingData[ 0 ] & MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
            == MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
        {
            IotLogWarn( "CONNACK session present bit set." );
            *pSessionPresent = true;

            /* MQTT 3.1.1 specifies that the fourth byte in CONNACK must be 0 if the
             * "Session Present" bit is set. */
            if( pRemainingData[ 1 ] != 0U )
            {
                status = MQTTBadResponse;
            }
        }
        else
        {
            IotLogInfo( "CONNACK session present bit not set." );
        }
    }

    if( status == MQTTSuccess )
    {
        /* In MQTT 3.1.1, only values 0 through 5 are valid CONNACK response codes. */
        if( pRemainingData[ 1 ] > 5U )
        {
            IotLogErrorWithArgs( "CONNACK response %hhu is not valid.",
                                 pRemainingData[ 1 ] );

            status = MQTTBadResponse;
        }
        else
        {
            /* Print the appropriate message for the CONNACK response code if logs are
             * enabled. */
            #if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
                _logConnackResponse( pRemainingData[ 1 ] );
            #endif

            /* A nonzero CONNACK response code means the connection was refused. */
            if( pRemainingData[ 1 ] > 0U )
            {
                status = MQTTServerRefused;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _readSubackStatus( size_t statusCount,
                                       const uint8_t * pStatusStart )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t subscriptionStatus = 0;
    size_t i = 0;

    assert( pStatusStart != NULL );

    /* Iterate through each status byte in the SUBACK packet. */
    for( i = 0; i < statusCount; i++ )
    {
        /* Read a single status byte in SUBACK. */
        subscriptionStatus = pStatusStart[ i ];

        /* MQTT 3.1.1 defines the following values as status codes. */
        switch( subscriptionStatus )
        {
            case 0x00:
            case 0x01:
            case 0x02:

                IotLogDebugWithArgs( "Topic filter %lu accepted, max QoS %hhu.",
                                     ( unsigned long ) i, subscriptionStatus );
                break;

            case 0x80:

                IotLogDebugWithArgs( "Topic filter %lu refused.", ( unsigned long ) i );

                /* Application should remove subscription from the list */
                status = MQTTServerRefused;

                break;

            default:
                IotLogDebugWithArgs( "Bad SUBSCRIBE status %hhu.", subscriptionStatus );

                status = MQTTBadResponse;

                break;
        }

        /* Stop parsing the subscription statuses if a bad response was received. */
        if( status == MQTTBadResponse )
        {
            break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _deserializeSuback( const MQTTPacketInfo_t * const pSuback,
                                        uint16_t * pPacketIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pSuback != NULL );
    assert( pPacketIdentifier != NULL );

    size_t remainingLength = pSuback->remainingLength;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;

    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least 1 return code. */
    if( remainingLength < 3U )
    {
        IotLogDebug( "SUBACK cannot have a remaining length less than 3." );
        status = MQTTBadResponse;
    }
    else
    {
        /* Extract the packet identifier (first 2 bytes of variable header) from SUBACK. */
        *pPacketIdentifier = UINT16_DECODE( pVariableHeader );

        IotLogDebugWithArgs( "Packet identifier %hu.", *pPacketIdentifier );

        status = _readSubackStatus( remainingLength - sizeof( uint16_t ),
                                    pVariableHeader + sizeof( uint16_t ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _deserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                         uint16_t * const pPacketId,
                                         MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pIncomingPacket != NULL );
    assert( pPacketId != NULL );
    assert( pPublishInfo != NULL );
    const uint8_t * pVariableHeader = pIncomingPacket->pRemainingData, * pPacketIdentifierHigh;
    /* The flags are the lower 4 bits of the first byte in PUBLISH. */
    status = _processPublishFlags( ( pIncomingPacket->type & 0x0FU ), pPublishInfo );

    if( status == MQTTSuccess )
    {
        /* Sanity checks for "Remaining length". A QoS 0 PUBLISH  must have a remaining
         * length of at least 3 to accommodate topic name length (2 bytes) and topic
         * name (at least 1 byte). A QoS 1 or 2 PUBLISH must have a remaining length of
         * at least 5 for the packet identifier in addition to the topic name length and
         * topic name. */
        status = _checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                               pPublishInfo->qos,
                                               MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0 );
    }

    if( status == MQTTSuccess )
    {
        /* Extract the topic name starting from the first byte of the variable header.
         * The topic name string starts at byte 3 in the variable header. */
        pPublishInfo->topicNameLength = UINT16_DECODE( pVariableHeader );

        /* Sanity checks for topic name length and "Remaining length". The remaining
         * length must be at least as large as the variable length header. */
        status = _checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                               pPublishInfo->qos,
                                               pPublishInfo->topicNameLength + sizeof( uint16_t ) );
    }

    if( status == MQTTSuccess )
    {
        /* Parse the topic. */
        pPublishInfo->pTopicName = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );
        IotLogDebugWithArgs( "Topic name length %hu: %.*s",
                             pPublishInfo->topicNameLength,
                             pPublishInfo->topicNameLength,
                             pPublishInfo->pTopicName );

        /* Extract the packet identifier for QoS 1 or 2 PUBLISH packets. Packet
         * identifier starts immediately after the topic name. */
        pPacketIdentifierHigh = ( const uint8_t * ) ( pPublishInfo->pTopicName + pPublishInfo->topicNameLength );

        if( pPublishInfo->qos > MQTTQoS0 )
        {
            *pPacketId = UINT16_DECODE( pPacketIdentifierHigh );

            IotLogDebugWithArgs( "Packet identifier %hu.", *pPacketId );

            /* Packet identifier cannot be 0. */
            if( *pPacketId == 0U )
            {
                status = MQTTBadResponse;
            }
        }
    }

    if( status == MQTTSuccess )
    {
        /* Calculate the length of the payload. QoS 1 or 2 PUBLISH packets contain
         * a packet identifier, but QoS 0 PUBLISH packets do not. */
        if( pPublishInfo->qos == MQTTQoS0 )
        {
            pPublishInfo->payloadLength = ( pIncomingPacket->remainingLength - pPublishInfo->topicNameLength - sizeof( uint16_t ) );
            pPublishInfo->pPayload = pPacketIdentifierHigh;
        }
        else
        {
            pPublishInfo->payloadLength = ( pIncomingPacket->remainingLength - pPublishInfo->topicNameLength - 2U * sizeof( uint16_t ) );
            pPublishInfo->pPayload = pPacketIdentifierHigh + sizeof( uint16_t );
        }

        IotLogDebugWithArgs( "Payload length %hu.", pPublishInfo->payloadLength );
    }
    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _deserializeSimpleAck( const MQTTPacketInfo_t * const pAck,
                                           uint16_t * pPacketIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pAck != NULL );
    assert( pPacketIdentifier != NULL );

    /* Check the "Remaining length" of the received ACK. */
    if( pAck->remainingLength != MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH )
    {
        IotLogErrorWithArgs( "ACK does not have remaining length of %d.",
                             MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH );

        status = MQTTBadResponse;
    }
    else
    {
        /* Extract the packet identifier (third and fourth bytes) from ACK. */
        *pPacketIdentifier = UINT16_DECODE( pAck->pRemainingData );

        IotLogDebugWithArgs( "Packet identifier %hu.", *pPacketIdentifier );

        /* Packet identifier cannot be 0. */
        if( *pPacketIdentifier == 0U )
        {
            status = MQTTBadResponse;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t _deserializePingresp( const MQTTPacketInfo_t * const pPingresp )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pPingresp != NULL );

    /* Check the "Remaining length" (second byte) of the received PINGRESP. */
    if( pPingresp->remainingLength != MQTT_PACKET_PINGRESP_REMAINING_LENGTH )
    {
        IotLogErrorWithArgs( "PINGRESP does not have remaining length of %d.",
                             MQTT_PACKET_PINGRESP_REMAINING_LENGTH );

        status = MQTTBadResponse;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t remainingLength;

    /* The CONNECT packet will always include a 10-byte variable header. */
    size_t connectPacketSize = MQTT_PACKET_CONNECT_HEADER_SIZE;

    /* Add the length of the client identifier. */
    connectPacketSize += pConnectInfo->clientIdentifierLength + sizeof( uint16_t );

    /* Add the lengths of the will message and topic name if provided. */
    if( pWillInfo != NULL )
    {
        connectPacketSize += pWillInfo->topicNameLength + sizeof( uint16_t ) +
                             pWillInfo->payloadLength + sizeof( uint16_t );
    }

    /* Add the lengths of the user name and password if provided. */
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
    connectPacketSize += 1U + _remainingLengthEncodedSize( connectPacketSize );

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

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t connectFlags = 0;
    uint8_t * pIndex = pBuffer->pBuffer;

    /* Check that the full packet size fits within the given buffer. */
    size_t connectPacketSize = remainingLength + _remainingLengthEncodedSize( remainingLength ) + 1U;

    if( connectPacketSize > pBuffer->size )
    {
        status = MQTTNoMemory;
    }

    if( status == MQTTSuccess )
    {
        /* The first byte in the CONNECT packet is the control packet type. */
        *pIndex = MQTT_PACKET_TYPE_CONNECT;
        pIndex++;

        /* The remaining length of the CONNECT packet is encoded starting from the
        * second byte. The remaining length does not include the length of the fixed
        * header or the encoding of the remaining length. */
        pIndex = _encodeRemainingLength( pIndex, remainingLength );

        /* The string "MQTT" is placed at the beginning of the CONNECT packet's variable
         * header. This string is 4 bytes long. */
        pIndex = _encodeString( pIndex, "MQTT", 4 );

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
        pIndex = _encodeString( pIndex,
                                pConnectInfo->pClientIdentifier,
                                pConnectInfo->clientIdentifierLength );

        /* Write the will topic name and message into the CONNECT packet if provided. */
        if( pWillInfo != NULL )
        {
            pIndex = _encodeString( pIndex,
                                    pWillInfo->pTopicName,
                                    pWillInfo->topicNameLength );
            pIndex = _encodeString( pIndex,
                                    pWillInfo->pPayload,
                                    ( uint16_t ) pWillInfo->payloadLength );
        }

        /* Encode the user name if provided. */
        if( pConnectInfo->pUserName != NULL )
        {
            pIndex = _encodeString( pIndex, pConnectInfo->pUserName, pConnectInfo->userNameLength );
        }

        /* Encode the password if provided. */
        if( pConnectInfo->pPassword != NULL )
        {
            pIndex = _encodeString( pIndex, pConnectInfo->pPassword, pConnectInfo->passwordLength );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SubscriptionPacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * const pPublishInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * const pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          const MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetDisconnectPacketSize( size_t * pPacketSize )
{
    /* MQTT DISCONNECT packets always have the same size. */
    *pPacketSize = MQTT_DISCONNECT_PACKET_SIZE;

    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t disconnectPacketSize;

    status = MQTT_GetDisconnectPacketSize( &disconnectPacketSize );

    if( status == MQTTSuccess )
    {
        if( pBuffer->size < disconnectPacketSize )
        {
            status = MQTTNoMemory;
        }
    }

    if( status == MQTTSuccess )
    {
        pBuffer->pBuffer[ 0 ] = MQTT_PACKET_TYPE_DISCONNECT;
        pBuffer->pBuffer[ 1 ] = MQTT_DISCONNECT_REMAINING_LENGTH;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * const pBuffer )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetIncomingPacket( MQTTTransportRecvFunc_t recvFunc,
                                     MQTTNetworkContext_t networkContext,
                                     MQTTPacketInfo_t * const pIncomingPacket )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == NULL ) || ( pPacketId == NULL ) || ( pPublishInfo == NULL ) )
    {
        IotLogErrorWithArgs( "Argument cannot be NULL: pIncomingPacket=%p, "
                             "pPacketId=%p, pPublishInfo=%p",
                             pIncomingPacket,
                             pPacketId,
                             pPublishInfo );
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->type & 0xF0U ) != MQTT_PACKET_TYPE_PUBLISH )
    {
        IotLogErrorWithArgs( "Packet is not publish. Packet type: %hu.",
                             pIncomingPacket->type );
        status = MQTTBadParameter;
    }
    else
    {
        status = _deserializePublish( pIncomingPacket, pPacketId, pPublishInfo );
    }
    
    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == NULL ) || ( pPacketId == NULL ) || ( pSessionPresent == NULL ) )
    {
        IotLogErrorWithArgs( "Argument cannot be NULL: pIncomingPacket=%p, "
                             "pPacketId=%p, pSessionPresent=%p",
                             pIncomingPacket,
                             pPacketId,
                             pSessionPresent );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->pRemainingData == NULL )
    {
        IotLogError( "Remaining data of incoming packet is NULL." );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->type == MQTT_PACKET_TYPE_PUBREL )
    {
        /* PUBREL is different in that its second bit must be set, so we
         * can't AND it with 0xF0. */
        status = _deserializeSimpleAck( pIncomingPacket, pPacketId );
    }
    else
    {
        /* Make sure response packet is a valid ack. */
        switch( pIncomingPacket->type & 0xF0U )
        {
            case MQTT_PACKET_TYPE_CONNACK:
                status = _deserializeConnack( pIncomingPacket, pSessionPresent );
                break;

            case MQTT_PACKET_TYPE_SUBACK:
                status = _deserializeSuback( pIncomingPacket, pPacketId );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                status = _deserializePingresp( pIncomingPacket );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBCOMP:
                status = _deserializeSimpleAck( pIncomingPacket, pPacketId );
                break;
            
            /* Any other packet type is invalid. */
            default:
                IotLogErrorWithArgs( "IotMqtt_DeserializeResponse() called with unknown packet type:(%lu).", pIncomingPacket->type );
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( MQTTTransportRecvFunc_t readFunc,
                                                  MQTTNetworkContext_t networkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;
    /* Read a single byte. */
    int32_t bytesReceived = readFunc( networkContext, &( pIncomingPacket->type ), 1U );
    if( bytesReceived == 1 )
    {
        /* Check validity. */
        if( _incomingPacketValid( pIncomingPacket->type ) )
        {
            pIncomingPacket->remainingLength = _getRemainingLength( readFunc, networkContext );

            if( pIncomingPacket->remainingLength == MQTT_REMAINING_LENGTH_INVALID )
            {
                status = MQTTBadResponse;
            }
        }
        else
        {
            IotLogErrorWithArgs( "Incoming packet invalid: Packet type=%u",
                                 pIncomingPacket->type );
            status = MQTTBadResponse;
        }
        
    }
    else
    {
        status = MQTTNoDataAvailable;
    }
    
    return status;
}

/*-----------------------------------------------------------*/
