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
#define SHADOW_OP_UPDATE_ACCEPTED               SHADOW_OP_UPDATE SHADOW_SUFFIX_ACCEPTED

/**
 * @brief The string representing "/shadow/update/rejected".
 */
#define SHADOW_OP_UPDATE_REJECTED               SHADOW_OP_UPDATE SHADOW_SUFFIX_REJECTED

/**
 * @brief The string representing "/shadow/update/delta".
 */
#define SHADOW_OP_UPDATE_DELTA                  SHADOW_OP_UPDATE SHADOW_SUFFIX_DELTA

/**
 * @brief The string representing "/shadow/update/document".
 */
#define SHADOW_OP_UPDATE_DOCUMENTS              SHADOW_OP_UPDATE SHADOW_SUFFIX_DOCUMENTS

/**
 * @brief The string representing "/shadow/delete/accepted".
 */
#define SHADOW_OP_DELETE_ACCEPTED               SHADOW_OP_DELETE SHADOW_SUFFIX_ACCEPTED

/**
 * @brief The string representing "/shadow/delete/accepted".
 */
#define SHADOW_OP_DELETE_REJECTED               SHADOW_OP_DELETE SHADOW_SUFFIX_REJECTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */
#define SHADOW_OP_GET_ACCEPTED                  SHADOW_OP_GET SHADOW_SUFFIX_ACCEPTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */
#define SHADOW_OP_GET_REJECTED                  SHADOW_OP_GET SHADOW_SUFFIX_REJECTED

/**
 * @brief The length of "/shadow/update/accepted".
 */
#define SHADOW_OP_UPDATE_ACCEPTED_LENGTH               ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_ACCEPTED_LENGTH )

/**
 * @brief The length of "/shadow/update/rejected".
 */
#define SHADOW_OP_UPDATE_REJECTED_LENGTH               ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_REJECTED_LENGTH )

/**
 * @brief The length of "/shadow/update/document".
 */
#define SHADOW_OP_UPDATE_DOCUMENTS_LENGTH              ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_DOCUMENTS_LENGTH )

/**
 * @brief The length of "/shadow/update/rejected".
 */
#define SHADOW_OP_UPDATE_DELTA_LENGTH                  ( SHADOW_OP_UPDATE_LENGTH + SHADOW_SUFFIX_DELTA_LENGTH )

/**
 * @brief The length of "/shadow/get/accepted".
 */
#define SHADOW_OP_GET_ACCEPTED_LENGTH                  ( SHADOW_OP_GET_LENGTH + SHADOW_SUFFIX_ACCEPTED_LENGTH )

/**
 * @brief The length of "/shadow/get/rejected".
 */
#define SHADOW_OP_GET_REJECTED_LENGTH                  ( SHADOW_OP_GET_LENGTH + SHADOW_SUFFIX_REJECTED_LENGTH )

/**
 * @brief The length of "/shadow/get/accepted".
 */
#define SHADOW_OP_DELETE_ACCEPTED_LENGTH               ( SHADOW_OP_DELETE_LENGTH + SHADOW_SUFFIX_ACCEPTED_LENGTH )

/**
 * @brief The length of "/shadow/delete/rejected".
 */
#define SHADOW_OP_DELETE_REJECTED_LENGTH               ( SHADOW_OP_DELETE_LENGTH + SHADOW_SUFFIX_REJECTED_LENGTH )

/**
 * @brief Determine if the string contains the substring.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[in] pSubString Pointer to the substring.
 * @param[in] subStringLength Length of pSubString.
 *
 * @return Return SHADOW_SUCCESS if it contains;
 *         return SHADOW_FAIL if not.
 */
static ShadowStatus_t containsSubString( const char * pString,
                                         uint16_t stringLength,
                                         const char * pSubString,
                                         uint16_t subStringLength );
/**
 * @brief Extract the Thing Name from a string.
 *
 * @param[in] pString Pointer to the starting of thing name.
 * @param[in] stringLength Length of pString.
 * @param[out] pThingNameLength Pointer to caller-supplied memory for returning the length of the Thing Name.
 *
 * @return Return SHADOW_SUCCESS if successfully extracted;
 *         return SHADOW_THINGNAME_PARSE_FAILED if failed.
 */
static ShadowStatus_t extractThingName( const char * pString,
                                        uint16_t stringLength,
                                        uint16_t * pThingNameLength );

/**
 * @brief Extract the Shadow message type from a string.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[out] pMessageType Pointer to call-supplied memory for returning the type of the shadow message.
 *
 * @return Return SHADOW_SUCCESS if successfully extracted;
 *         return SHADOW_SHADOW_MESSAGE_TYPE_PARSE_FAILED if failed.
 */
static ShadowStatus_t extractShadowMessageType( const char * pString,
                                                uint16_t stringLength,
                                                ShadowMessageType_t * pMessageType );

/**
 * @brief Get the shadow operation string for a given shadow topic type.
 *
 * @param[in] topicType The given shadow topic type.
 *
 * @return The shadow operation string for the given shadow type.
 */
static const char * getShadowOperationString( ShadowTopicStringType_t topicType );

/**
 * @brief Get the shadow operation string length for a given shadow topic type.
 *
 * @param[in] topicType The given shadow topic type.
 *
 * @return The shadow operation string length for the given shadow type.
 */
static uint16_t getShadowOperationLength( ShadowTopicStringType_t topicType );

/*-----------------------------------------------------------*/

static ShadowStatus_t containsSubString( const char * pString,
                                         uint16_t stringLength,
                                         const char * pSubString,
                                         uint16_t subStringLength )
{
    ShadowStatus_t returnStatus = SHADOW_FAIL;

    /* The string must be at least as long as the substring to contain it
     * completely. */
    if( stringLength >= subStringLength )
    {
        /* We are only checking up to subStringLength characters in the original
         * string. The string may be longer and contain additional characters. */
        if( strncmp( pString, pSubString, ( size_t  ) subStringLength ) == 0 )
        {
            returnStatus = SHADOW_SUCCESS;
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static ShadowStatus_t extractThingName( const char * pString,
                                        uint16_t stringLength,
                                        uint16_t * pThingNameLength )
{
    uint16_t index = 0U;
    ShadowStatus_t returnStatus = SHADOW_THINGNAME_PARSE_FAILED;

    for( ; index < stringLength; index++ )
    {
        if( pString[ index ] == ( char ) '/' )
        {
            break;
        }
    }

    /* Zero length thing name is not valid,
     * $"$aws/things/<ThingName>/
     * $"$aws/things/<ThingName>"
     * will extract the same thing name result.
     * Only empty thing name string like:
     * "$aws/things/" or "$aws/things" will fail.
     */
    if( index > 0U )
    {
        * pThingNameLength = index;
        returnStatus = SHADOW_SUCCESS;
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static ShadowStatus_t extractShadowMessageType( const char * pString,
                                                uint16_t stringLength,
                                                ShadowMessageType_t * pMessageType )
{
    uint32_t index = 0U;
    ShadowStatus_t returnStatus = SHADOW_FAIL;

    /* Lookup table for Shadow message string. */
    static const char * const pMessageStrings[ ShadowMessageTypeMaxNum ] =
    {
        SHADOW_OP_GET_ACCEPTED,
        SHADOW_OP_GET_REJECTED,
        SHADOW_OP_DELETE_ACCEPTED,
        SHADOW_OP_DELETE_REJECTED,
        SHADOW_OP_UPDATE_ACCEPTED,
        SHADOW_OP_UPDATE_REJECTED,
        SHADOW_OP_UPDATE_DOCUMENTS,
        SHADOW_OP_UPDATE_DELTA
    };

    /* Lookup table for Shadow message string length. */
    static const uint16_t pMessageStringsLength[ ShadowMessageTypeMaxNum ] =
    {
        SHADOW_OP_GET_ACCEPTED_LENGTH,
        SHADOW_OP_GET_REJECTED_LENGTH,
        SHADOW_OP_DELETE_ACCEPTED_LENGTH,
        SHADOW_OP_DELETE_REJECTED_LENGTH,
        SHADOW_OP_UPDATE_ACCEPTED_LENGTH,
        SHADOW_OP_UPDATE_REJECTED_LENGTH,
        SHADOW_OP_UPDATE_DOCUMENTS_LENGTH,
        SHADOW_OP_UPDATE_DELTA_LENGTH
    };

    /* Lookup table for Shadow message types. */
    static const ShadowMessageType_t pMessageTypes[ ShadowMessageTypeMaxNum ] =
    {
        ShadowMessageTypeGetAccepted ,
        ShadowMessageTypeGetRejected,
        ShadowMessageTypeDeleteAccepted,
        ShadowMessageTypeDeleteRejected,
        ShadowMessageTypeUpdateAccepted,
        ShadowMessageTypeUpdateRejected,
        ShadowMessageTypeUpdateDocuments,
        ShadowMessageTypeUpdateDelta
    };

    for( ; index < ( uint32_t ) ( sizeof( pMessageStrings ) / sizeof( pMessageStrings[0] ) ); index++ )
    {
        returnStatus = containsSubString( pString,
                                          stringLength,
                                          pMessageStrings[ index ],
                                          pMessageStringsLength[ index ] );

        /* If the operation string matches, there must not be any other extra
         * character remaining in the string. */
        if( returnStatus == SHADOW_SUCCESS )
        {
            if( stringLength != pMessageStringsLength[ index ] )
            {
                returnStatus = SHADOW_FAIL;
            }
            else
            {
                * pMessageType = pMessageTypes[ index ];
                break;
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static const char * getShadowOperationString( ShadowTopicStringType_t topicType )
{
    const char *shadowOperationString = NULL;

    switch( topicType )
    {
        case ShadowTopicStringTypeGet:
        {
            shadowOperationString = SHADOW_OP_GET;
            break;
        }
        case ShadowTopicStringTypeGetAccepted:
        {
            shadowOperationString = SHADOW_OP_GET_ACCEPTED;
            break;
        }
        case ShadowTopicStringTypeGetRejected:
        {
            shadowOperationString = SHADOW_OP_GET_REJECTED;
            break;
        }
        case ShadowTopicStringTypeDelete:
        {
            shadowOperationString = SHADOW_OP_DELETE;
            break;
        }
        case ShadowTopicStringTypeDeleteAccepted:
        {
            shadowOperationString = SHADOW_OP_DELETE_ACCEPTED;
            break;
        }
        case ShadowTopicStringTypeDeleteRejected:
        {
            shadowOperationString = SHADOW_OP_DELETE_REJECTED;
            break;
        }
        case ShadowTopicStringTypeUpdate:
        {
            shadowOperationString = SHADOW_OP_UPDATE;
            break;
        }
        case ShadowTopicStringTypeUpdateAccepted:
        {
            shadowOperationString = SHADOW_OP_UPDATE_ACCEPTED;
            break;
        }
        case ShadowTopicStringTypeUpdateRejected:
        {
            shadowOperationString = SHADOW_OP_UPDATE_REJECTED;
            break;
        }
        case ShadowTopicStringTypeUpdateDocuments:
        {
            shadowOperationString = SHADOW_OP_UPDATE_DOCUMENTS;
            break;
        }
        case ShadowTopicStringTypeUpdateDelta:
        {
            shadowOperationString = SHADOW_OP_UPDATE_DELTA;
            break;
        }
        default:
        {
            LogError( ( "Unexpected  topicType: %u", topicType ) );
            shadowOperationString = NULL;
            break;
        }
    }

    return shadowOperationString;
}

/*-----------------------------------------------------------*/

static uint16_t getShadowOperationLength( ShadowTopicStringType_t topicType )
{
    uint16_t shadowOperationLength = 0U;

    switch( topicType )
    {
        case ShadowTopicStringTypeGet:
        {
            shadowOperationLength = SHADOW_OP_GET_LENGTH;
            break;
        }
        case ShadowTopicStringTypeGetAccepted:
        {
            shadowOperationLength = SHADOW_OP_GET_ACCEPTED_LENGTH;
            break;
        }
        case ShadowTopicStringTypeGetRejected:
        {
            shadowOperationLength = SHADOW_OP_GET_REJECTED_LENGTH;
            break;
        }
        case ShadowTopicStringTypeDelete:
        {
            shadowOperationLength = SHADOW_OP_DELETE_LENGTH;
            break;
        }
        case ShadowTopicStringTypeDeleteAccepted:
        {
            shadowOperationLength = SHADOW_OP_DELETE_ACCEPTED_LENGTH;
            break;
        }
        case ShadowTopicStringTypeDeleteRejected:
        {
            shadowOperationLength = SHADOW_OP_DELETE_REJECTED_LENGTH;
            break;
        }
        case ShadowTopicStringTypeUpdate:
        {
            shadowOperationLength = SHADOW_OP_UPDATE_LENGTH;
            break;
        }
        case ShadowTopicStringTypeUpdateAccepted:
        {
            shadowOperationLength = SHADOW_OP_UPDATE_ACCEPTED_LENGTH;
            break;
        }
        case ShadowTopicStringTypeUpdateRejected:
        {
            shadowOperationLength = SHADOW_OP_UPDATE_REJECTED_LENGTH;
            break;
        }
        case ShadowTopicStringTypeUpdateDocuments:
        {
            shadowOperationLength = SHADOW_OP_UPDATE_DOCUMENTS_LENGTH;
            break;
        }
        case ShadowTopicStringTypeUpdateDelta:
        {
            shadowOperationLength = SHADOW_OP_UPDATE_DELTA_LENGTH;
            break;
        }
        default:
        {
            LogError( ( "Unexpected  topicType: %u", topicType ) );
            break;
        }
    }

    return shadowOperationLength;
}

/*-----------------------------------------------------------*/

/*-----------------------------------------------------------*/

ShadowStatus_t Shadow_MatchTopic( const char * pTopic,
                                  uint16_t topicLength,
                                  ShadowMessageType_t * pMessageType,
                                  const char ** pThingName,
                                  uint16_t * pThingNameLength )
{
    uint16_t consumedTopicLength = 0U;
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;

    if( ( pTopic == NULL ) ||
        ( topicLength == 0U ) ||
        ( pMessageType == NULL ) ||
        ( pThingName == NULL ) ||
        ( pThingNameLength == NULL ) )
    {
        shadowStatus = SHADOW_BAD_PARAMETER;
        LogError( ( "Invalid input parameters pTopic: %p, topicLength: %u, pMessageType: %p, pThingName: %p, pThingNameLength: %p",
                    pTopic,
                    topicLength,
                    pMessageType,
                    pThingName,
                    pThingNameLength ) );
    }

    /* A shadow topic string takes one of the two forms:
     *   $aws/things/<thingName>/shadow/<operation>
     *   $aws/things/<thingName>/shadow/<operation>/<suffix>
     *
     * We need to match the following things:
     * 1. Prefix ($aws/things).
     * 2. Thing Name.
     * 3. Shadow operation and suffix.
     */
    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* First match the prefix. */
        shadowStatus = containsSubString( & ( pTopic[ consumedTopicLength ] ),
                                          topicLength - consumedTopicLength,
                                          SHADOW_PREFIX,
                                          SHADOW_PREFIX_LENGTH );
        if( shadowStatus == SHADOW_SUCCESS )
        {
            consumedTopicLength += SHADOW_PREFIX_LENGTH;

            /* If no more topic string is left to parse, fail. */
            if( consumedTopicLength >= topicLength )
            {
                shadowStatus = SHADOW_THINGNAME_PARSE_FAILED;
                LogDebug( ( "Not related to Shadow, thing name is not in pTopic %s, failed to parse thing name", pTopic ) );
            }
        }
        else
        {
            LogDebug( ( "Not related to Shadow, failed to parse shadow topic prefix in pTopic %s", pTopic ) );
        }
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* Extract thing name. */
        shadowStatus = extractThingName( & ( pTopic[ consumedTopicLength ] ),
                                         topicLength - consumedTopicLength,
                                         pThingNameLength );
        if( shadowStatus == SHADOW_SUCCESS )
        {
            /* Update the out parameter if we successfully extracted the thing name. */
            * pThingName = & ( pTopic[ consumedTopicLength ] );

            consumedTopicLength += * pThingNameLength;

            /* If no more topic string is left to parse, fail. */
            if( consumedTopicLength >= topicLength )
            {
                shadowStatus = SHADOW_SHADOW_MESSAGE_TYPE_PARSE_FAILED;
                LogDebug( ( "Not related to Shadow, shadow message type is not in pTopic %s, failed to parse shadow message type", pTopic ) );
            }
        }
        else
        {
            LogDebug( ( "Not related to Shadow, failed to parse thing name in pTopic %s", pTopic ) );
        }
    }

    if( shadowStatus == SHADOW_SUCCESS )
    {
        /* Extract shadow message type. */
        shadowStatus = extractShadowMessageType( & ( pTopic[ consumedTopicLength ] ),
                                                 topicLength - consumedTopicLength,
                                                 pMessageType );
        if( shadowStatus != SHADOW_SUCCESS )
        {
            LogDebug( ( "Not related to Shadow, failed to match shadow message type in pTopic %s", pTopic ) );
        }
    }

    return shadowStatus;
}
/*-----------------------------------------------------------*/

ShadowStatus_t Shadow_GetTopicString( ShadowTopicStringType_t topicType,
                                      const char * pThingName,
                                      uint8_t thingNameLength,
                                      char * pTopicBuffer,
                                      uint16_t bufferSize,
                                      uint16_t * pOutLength )
{
    uint16_t offset = 0U, generatedTopicStringLength = 0U, operationStringLength = 0U;
    ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
    const char * pOperationString = NULL;

    if( ( pTopicBuffer == NULL ) ||
        ( pThingName == NULL ) ||
        ( thingNameLength == 0U ) ||
        ( topicType >= ShadowTopicStringTypeMaxNum ) ||
        ( pOutLength == NULL ) )
    {
        shadowStatus = SHADOW_BAD_PARAMETER;
        LogError( ( "Invalid input parameters pTopicBuffer: %p, pThingName: %p, thingNameLength: %u, topicType: %u, pOutLength: %p",
                    pTopicBuffer,
                    pThingName,
                    thingNameLength,
                    topicType,
                    pOutLength ) );
    }
    else
    {
        generatedTopicStringLength = SHADOW_PREFIX_LENGTH +           /* Prefix ("$aws/things/"). */
                                     thingNameLength +                      /* Thing name. */
                                     getShadowOperationLength( topicType ); /* Shadow operation. */

        if( bufferSize < generatedTopicStringLength )
        {
            shadowStatus = SHADOW_BUFFER_TOO_SMALL;
            LogError( ( "Input bufferSize too small, bufferSize %d, required ", bufferSize, generatedTopicStringLength) );
        }
        else
        {
            /* Copy the Shadow topic prefix into the topic buffer. */
            ( void ) memcpy( ( void * ) pTopicBuffer,
                             ( const void * ) SHADOW_PREFIX,
                             ( size_t ) SHADOW_PREFIX_LENGTH );
            offset = ( uint16_t ) ( offset + SHADOW_PREFIX_LENGTH );

            /* Copy the Thing Name into the topic buffer. */
            ( void ) memcpy( ( void * ) & ( pTopicBuffer[ offset ] ),
                             ( const void * ) pThingName,
                             ( size_t ) thingNameLength );
            offset = ( uint16_t ) ( offset + thingNameLength );

            pOperationString = getShadowOperationString( topicType );
            operationStringLength = getShadowOperationLength( topicType );
            /* Copy the Shadow operation string into the topic buffer. */
            ( void ) memcpy( ( void * ) & ( pTopicBuffer[ offset ] ),
                             ( const void * ) pOperationString,
                             ( size_t ) operationStringLength );

            /* Return the generated topic string length to the caller. */
            * pOutLength = generatedTopicStringLength;
        }
    }

    return shadowStatus;
}
/*-----------------------------------------------------------*/
