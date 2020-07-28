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

/**
 * @file shadow.c
 * @brief Implements the user-facing functions of the Shadow library.
 */

/* Standard includes. */
#include <stdbool.h>
#include <string.h>

/* Shadow includes. */
#include "shadow.h"

/**
 * @brief The string representing "/shadow/update/accepted".
 */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_ACCEPTED               SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_ACCEPTED

/**
 * @brief The string representing "/shadow/update/rejected".
 */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_REJECTED               SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_REJECTED

/**
 * @brief The string representing "/shadow/update/delta".
 */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_DELTA                  SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_DELTA

/**
 * @brief The string representing "/shadow/update/document".
 */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_DOCUMENTS              SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_DOCUMENTS

/**
 * @brief The string representing "/shadow/delete/accepted".
 */
#define SHADOW_TOPIC_OPERATION_STRING_DELETE_ACCEPTED               SHADOW_TOPIC_OPERATION_STRING_DELETE SHADOW_TOPIC_SUFFIX_STRING_ACCEPTED

/**
 * @brief The string representing "/shadow/delete/accepted".
 */
#define SHADOW_TOPIC_OPERATION_STRING_DELETE_REJECTED               SHADOW_TOPIC_OPERATION_STRING_DELETE SHADOW_TOPIC_SUFFIX_STRING_REJECTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */
#define SHADOW_TOPIC_OPERATION_STRING_GET_ACCEPTED                  SHADOW_TOPIC_OPERATION_STRING_GET SHADOW_TOPIC_SUFFIX_STRING_ACCEPTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */
#define SHADOW_TOPIC_OPERATION_STRING_GET_REJECTED                  SHADOW_TOPIC_OPERATION_STRING_GET SHADOW_TOPIC_SUFFIX_STRING_REJECTED

/**
 * @brief The length of "/shadow/update/accepted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_ACCEPTED               ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_ACCEPTED )

/**
 * @brief The length of "/shadow/update/rejcted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_REJECTED               ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_REJECTED )

/**
 * @brief The length of "/shadow/update/document".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DOCUMENTS              ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_DOCUMENTS )

/**
 * @brief The length of "/shadow/update/rejcted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DELTA                  ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_DELTA )

/**
 * @brief The length of "/shadow/get/accepted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_GET_ACCEPTED                  ( SHADOW_TOPIC_OPERATION_LENGTH_GET + SHADOW_TOPIC_SUFFIX_LENGTH_ACCEPTED )

/**
 * @brief The length of "/shadow/get/rejcted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_GET_REJECTED                  ( SHADOW_TOPIC_OPERATION_LENGTH_GET + SHADOW_TOPIC_SUFFIX_LENGTH_REJECTED )

/**
 * @brief The length of "/shadow/get/accepted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_DELETE_ACCEPTED               ( SHADOW_TOPIC_OPERATION_LENGTH_DELETE + SHADOW_TOPIC_SUFFIX_LENGTH_ACCEPTED )

/**
 * @brief The length of "/shadow/delete/rejcted".
 */
#define SHADOW_TOPIC_OPERATION_LENGTH_DELETE_REJECTED               ( SHADOW_TOPIC_OPERATION_LENGTH_DELETE + SHADOW_TOPIC_SUFFIX_LENGTH_REJECTED )


/**
 * @brief Given the topic string of an incoming message, determine whether it is 
 *        related to a device shadow.
 *
 * @brief param[in] pTopic Pointer to the MQTT topic string.
 * @brief param[in] topicLength Length of pTopic.
 * @brief param[in] thingNameLength The thing name length.
 *
 * @return Return ShadowMessageTypeMaxNum if not match is founded;
 *         return the corresponding ShadowMessageType_t type if found match.
 */
static ShadowMessageType_t validateShadowMessageType( const char * pTopic,
                                                      uint16_t topicLength,
                                                      uint8_t thingNameLength );


/*-----------------------------------------------------------*/

static ShadowMessageType_t validateShadowMessageType( const char * pTopic,
                                                      uint16_t topicLength,
                                                      uint8_t thingNameLength )
{
    const char * pMessageTypeStart = NULL;
    ShadowMessageType_t ret = ShadowMessageTypeMaxNum;
    ShadowMessageType_t index = ShadowMessageTypeGetAccepted;

    /* Lookup table for Shadow message string. */
    static const char * pMessageString[ ShadowMessageTypeMaxNum ] =
    {
        SHADOW_TOPIC_OPERATION_STRING_GET_ACCEPTED,
        SHADOW_TOPIC_OPERATION_STRING_GET_REJECTED,
        SHADOW_TOPIC_OPERATION_STRING_DELETE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_STRING_DELETE_REJECTED,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_REJECTED,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_DOCUMENTS,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_DELTA
    };

    /* Lookup table for Shadow message string length. */
    static const uint16_t pMessageStringLength[ ShadowMessageTypeMaxNum ] =
    {
        SHADOW_TOPIC_OPERATION_LENGTH_GET_ACCEPTED,
        SHADOW_TOPIC_OPERATION_LENGTH_GET_REJECTED,
        SHADOW_TOPIC_OPERATION_LENGTH_DELETE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_LENGTH_DELETE_REJECTED,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_REJECTED,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DOCUMENTS,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DELTA
    };

    /* The message type starts immediately after "$aws/things/<thingName>/". */
    pMessageTypeStart = pTopic + ( uint8_t ) SHADOW_TOPIC_PREFIX_LENGTH + thingNameLength;

    for( ; index < ShadowMessageTypeMaxNum; index++ )
    {
        if( ( SHADOW_TOPIC_PREFIX_LENGTH + thingNameLength + \
              pMessageStringLength[ index ] ) == topicLength )
        {
            /* strncmp uses char * as input, casting typedef to char. */
            /* coverity[misra_c_2012_directive_4_6_violation] */
            if( strncmp( pMessageTypeStart, pMessageString[ index ], pMessageStringLength[ index ] ) == 0 )
            {
                ret = index;
                break;
            }
        }
    }

    return ret;
}

ShadowStatus_t Shadow_MatchTopic( const char * pTopic,
                                  uint16_t topicLength,
                                  ShadowMessageType_t * pMessageType,
                                  const char ** pThingName,
                                  uint8_t * pThingNameLength )
{
    uint8_t thingNameLength = 0U;
    const char * pThingNameStart = NULL;
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;

    if( ( pTopic == NULL ) || ( topicLength == 0U ) ||
        ( pMessageType == NULL ) || ( pThingNameLength == NULL ) )
    {
        shadowStatus = SHADOW_STATUS_BAD_PARAMETER;
    }
    else
    {
        /* The Thing Name starts immediately after the topic prefix. */
         pThingNameStart = pTopic + SHADOW_TOPIC_PREFIX_LENGTH;

        /* Calculate the length of the Thing Name, which is terminated with a '/'. */
        while( ( ( thingNameLength + SHADOW_TOPIC_PREFIX_LENGTH ) < topicLength ) &&
               ( pThingNameStart[ thingNameLength ] != '/' ) )
        {
            thingNameLength++;
        }

        if( thingNameLength > 0U )
        {
            * pThingName = pThingNameStart;
            * pThingNameLength = thingNameLength;
        }
        else
        {
            shadowStatus = SHADOW_STATUS_THINGNAME_PARSE_FAILED;
        }

        if( shadowStatus == SHADOW_STATUS_SUCCESS )
        {
            messageType = validateShadowMessageType( pTopic, topicLength, thingNameLength );
            if( messageType == ShadowMessageTypeMaxNum )
            {
                shadowStatus = SHADOW_STATUS_FAIL;
            }
            else
            {
                * pMessageType = messageType;
            }
        }
    } 

    return shadowStatus;
}

ShadowStatus_t Shadow_GetTopicString( ShadowTopicStringType_t topicType,
                                      const char * pThingName,
                                      uint8_t thingNameLength,
                                      char * pTopicBuffer,
                                      uint16_t bufferSize,
                                      uint16_t * pOutLength )
{
    uint16_t offset = 0U;
    ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;

    /* Lookup table for Shadow operation string. */
    static const char * pTopicString[ SHADOW_TOPIC_STRING_TYPE_MAX_NUM ] =
    {
        SHADOW_TOPIC_OPERATION_STRING_GET,
        SHADOW_TOPIC_OPERATION_STRING_GET_ACCEPTED,
        SHADOW_TOPIC_OPERATION_STRING_GET_REJECTED,
        SHADOW_TOPIC_OPERATION_STRING_DELETE,
        SHADOW_TOPIC_OPERATION_STRING_DELETE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_STRING_DELETE_REJECTED,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_REJECTED,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_DOCUMENTS,
        SHADOW_TOPIC_OPERATION_STRING_UPDATE_DELTA
    };

    /* Lookup table for Shadow operation string length. */
    static const uint16_t pTopicStringLength[ SHADOW_TOPIC_STRING_TYPE_MAX_NUM ] =
    {
        SHADOW_TOPIC_OPERATION_LENGTH_GET,
        SHADOW_TOPIC_OPERATION_LENGTH_GET_ACCEPTED,
        SHADOW_TOPIC_OPERATION_LENGTH_GET_REJECTED,
        SHADOW_TOPIC_OPERATION_LENGTH_DELETE,
        SHADOW_TOPIC_OPERATION_LENGTH_DELETE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_LENGTH_DELETE_REJECTED,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_ACCEPTED,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_REJECTED,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DOCUMENTS,
        SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DELTA
    };

    if( ( pTopicBuffer == NULL ) || ( pThingName == NULL ) ||
        ( thingNameLength == 0U ) || ( topicType >= SHADOW_TOPIC_STRING_TYPE_MAX_NUM ) ||
        ( pOutLength == NULL ) )
    {
        shadowStatus = SHADOW_STATUS_BAD_PARAMETER;
    }
    else if( bufferSize < ( SHADOW_TOPIC_PREFIX_LENGTH + pTopicStringLength[ topicType ] +  thingNameLength ) )
    {
        shadowStatus = SHADOW_STATUS_INVALID_BUFFER_LENGTH;
    }
    else 
    {
        /* Copy the Shadow topic prefix into the topic buffer. */
        ( void ) memcpy( ( void * ) pTopicBuffer, SHADOW_TOPIC_PREFIX_STRING, SHADOW_TOPIC_PREFIX_LENGTH );
        offset = ( uint16_t ) ( offset + SHADOW_TOPIC_PREFIX_LENGTH );

        /* Copy the Thing Name into the topic buffer. */
        ( void ) memcpy( ( void * ) pTopicBuffer + offset, pThingName, thingNameLength );
        offset = ( uint16_t ) ( offset + thingNameLength );
        /* Copy the Shadow operation string into the topic buffer. */
        ( void ) memcpy( ( void * ) ( pTopicBuffer + offset ),
                         pTopicString[ topicType ],
                         pTopicStringLength[ topicType ] );
        * pOutLength = ( offset + pTopicStringLength[ topicType ] );
    }

    return shadowStatus;
}
/*-----------------------------------------------------------*/
