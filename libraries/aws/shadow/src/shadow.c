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

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _ACCEPTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_ACCEPTED               SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_ACCEPTED

/**
 * @brief The string representing "/shadow/update/rejected".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _REJECTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_REJECTED               SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_REJECTED

/**
 * @brief The string representing "/shadow/update/delta".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _DELTA suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_DELTA                  SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_DELTA

/**
 * @brief The string representing "/shadow/update/document".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without DOCUMENTS suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_UPDATE_DOCUMENTS              SHADOW_TOPIC_OPERATION_STRING_UPDATE SHADOW_TOPIC_SUFFIX_STRING_DOCUMENTS

/**
 * @brief The string representing "/shadow/delete/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _ACCEPTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_DELETE_ACCEPTED               SHADOW_TOPIC_OPERATION_STRING_DELETE SHADOW_TOPIC_SUFFIX_STRING_ACCEPTED

/**
 * @brief The string representing "/shadow/delete/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _REJECTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_DELETE_REJECTED               SHADOW_TOPIC_OPERATION_STRING_DELETE SHADOW_TOPIC_SUFFIX_STRING_REJECTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _ACCEPTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_GET_ACCEPTED                  SHADOW_TOPIC_OPERATION_STRING_GET SHADOW_TOPIC_SUFFIX_STRING_ACCEPTED

/**
 * @brief The string representing "/shadow/get/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _REJECTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_STRING_GET_REJECTED                  SHADOW_TOPIC_OPERATION_STRING_GET SHADOW_TOPIC_SUFFIX_STRING_REJECTED

/**
 * @brief The length of "/shadow/update/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _ACCEPTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_ACCEPTED               ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_ACCEPTED )

/**
 * @brief The length of "/shadow/update/rejected".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _REJECTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_REJECTED               ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_REJECTED )

/**
 * @brief The length of "/shadow/update/document".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without DOCUMENTS suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DOCUMENTS              ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_DOCUMENTS )

/**
 * @brief The length of "/shadow/update/rejected".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _DELTA suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_UPDATE_DELTA                  ( SHADOW_TOPIC_OPERATION_LENGTH_UPDATE + SHADOW_TOPIC_SUFFIX_LENGTH_DELTA )

/**
 * @brief The length of "/shadow/get/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _ACCEPTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_GET_ACCEPTED                  ( SHADOW_TOPIC_OPERATION_LENGTH_GET + SHADOW_TOPIC_SUFFIX_LENGTH_ACCEPTED )

/**
 * @brief The length of "/shadow/get/rejected".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _REJECTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_GET_REJECTED                  ( SHADOW_TOPIC_OPERATION_LENGTH_GET + SHADOW_TOPIC_SUFFIX_LENGTH_REJECTED )

/**
 * @brief The length of "/shadow/get/accepted".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _ACCEPTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_DELETE_ACCEPTED               ( SHADOW_TOPIC_OPERATION_LENGTH_DELETE + SHADOW_TOPIC_SUFFIX_LENGTH_ACCEPTED )

/**
 * @brief The length of "/shadow/delete/rejected".
 */

/* MISRA Rule 5.4 flags the following macro's name as ambiguous from the
 * one without _REJECTED suffix. This rule is suppressed for naming consistency with
 * other Shadow header field and value string and length macros in this file.*/
/* coverity[misra_c_2012_rule_5_4_violation] */
#define SHADOW_TOPIC_OPERATION_LENGTH_DELETE_REJECTED               ( SHADOW_TOPIC_OPERATION_LENGTH_DELETE + SHADOW_TOPIC_SUFFIX_LENGTH_REJECTED )

/**
 * @brief Determine if the string contains the substring.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[in] pSubString Pointer to the substring.
 * @param[in] subStringLength Length of pSubString.
 *
 * @return Return SHADOW_STATUS_SUCCESS if it contains;
 *         return SHADOW_STATUS_FAIL if not.
 */
static ShadowStatus_t containsSubString( const char * pString,
                                         uint16_t stringLength,
                                         const char * pSubString,
                                         uint16_t subStringLength );
/**
 * @brief Extract the Thing Name from a string.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[out] pThingName Points to the 1st character of Thing Name inside of the topic string.
 * @param[out] pThingNameLength Pointer to caller-supplied memory for returning the length of the Thing Name.
 *
 * @return Return SHADOW_STATUS_SUCCESS if successfully extracted;
 *         return SHADOW_STATUS_THINGNAME_PARSE_FAILED if failed.
 */
static ShadowStatus_t extractThingName( const char * pString,
                                        uint16_t stringLength,
                                        const char ** pThingName,
                                        uint16_t * pThingNameLength );

/**
 * @brief Extract the Shadow message type from a string.
 *
 * @param[in] pString Pointer to the string.
 * @param[in] stringLength Length of pString.
 * @param[out] pMessageType Pointer to call-supplied memory for returning the type of the shadow message.
 *
 * @return Return SHADOW_STATUS_SUCCESS if successfully extracted;
 *         return SHADOW_STATUS_SHADOW_MESSAGE_TYPE_PARSE_FAILED if failed.
 */
static ShadowStatus_t extractShadowMessageType( const char * pString,
                                                uint16_t stringLength,
                                                ShadowMessageType_t * pMessageType );
/*-----------------------------------------------------------*/

static ShadowStatus_t containsSubString( const char * pString,
                                         uint16_t stringLength,
                                         const char * pSubString,
                                         uint16_t subStringLength )
{
    ShadowStatus_t returnStatus = SHADOW_STATUS_FAIL;

    /* The string must be at least as long as the substring to contain it
     * completely. */
    if( stringLength >= subStringLength )
    {
        /* We are only checking up to subStringLength characters in the original
         * string. The string may be longer and contain additional characters. */
        if( strncmp( pString, pSubString, ( size_t  ) subStringLength ) == 0 )
        {
            returnStatus = SHADOW_STATUS_SUCCESS;
        }
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static ShadowStatus_t extractThingName( const char * pString,
                                        uint16_t stringLength,
                                        const char ** pThingName,
                                        uint16_t * pThingNameLength )
{
    uint16_t index = 0U;
    ShadowStatus_t returnStatus = SHADOW_STATUS_THINGNAME_PARSE_FAILED;

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
        * pThingName = pString;
        * pThingNameLength = index;
        returnStatus = SHADOW_STATUS_SUCCESS;
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

static ShadowStatus_t extractShadowMessageType( const char * pString,
                                                uint16_t stringLength,
                                                ShadowMessageType_t * pMessageType )
{
    uint32_t index = 0U;
    ShadowStatus_t returnStatus = SHADOW_STATUS_FAIL;

    /* Lookup table for Shadow message string. */
    static const char * const pMessageStrings[ ShadowMessageTypeMaxNum ] =
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
    static const uint16_t pMessageStringsLength[ ShadowMessageTypeMaxNum ] =
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

    /* Lookup table for Shadow message types. */
    static const ShadowMessageType_t pMessageTypes[ ShadowMessageTypeMaxNum ] =
    {
        ShadowMessageTypeGetAccepted ,
        ShadowMessageTypeGetRejected,
        ShadowMessageTypeDeleteAccepted,
        ShadowMessageTypeDeleteRejected,
        ShadowMessageTypeUpdateAccepted,
        ShadowMessageTypeUpdateRejected,
        ShadowMessageTypeUpdateDocument,
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
        if( returnStatus == SHADOW_STATUS_SUCCESS )
        {
            if( stringLength != pMessageStringsLength[ index ] )
            {
                returnStatus = SHADOW_STATUS_FAIL;
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

ShadowStatus_t Shadow_MatchTopic( const char * pTopic,
                                  uint16_t topicLength,
                                  ShadowMessageType_t * pMessageType,
                                  const char ** pThingName,
                                  uint16_t * pThingNameLength )
{
    uint16_t consumedTopicLength = 0U;
    ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;

    if( ( pTopic == NULL ) ||
        ( topicLength == 0U ) ||
        ( pMessageType == NULL ) ||
        ( pThingName == NULL ) ||
        ( pThingNameLength == NULL ) )
    {
        shadowStatus = SHADOW_STATUS_BAD_PARAMETER;
        LogError( ( "Invalid input parameters" ) );
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
    if( shadowStatus == SHADOW_STATUS_SUCCESS )
    {
        /* First match the prefix. */
        shadowStatus = containsSubString( & ( pTopic[ consumedTopicLength ] ),
                                          topicLength - consumedTopicLength,
                                          SHADOW_TOPIC_PREFIX_STRING,
                                          SHADOW_TOPIC_PREFIX_LENGTH );
        if( shadowStatus == SHADOW_STATUS_SUCCESS )
        {
            consumedTopicLength += SHADOW_TOPIC_PREFIX_LENGTH;

            /* If no more topic string is left to parse, fail. */
            if( consumedTopicLength >= topicLength )
            {
                shadowStatus = SHADOW_STATUS_THINGNAME_PARSE_FAILED;
                LogDebug( ( "Not related to Shadow, thing name is not in pTopic %s, failed to parse thing name", pTopic ) );
            }
        }
        else
        {
            LogDebug( ( "Not related to Shadow, failed to parse shadow topic prefix in pTopic %s", pTopic ) );
        }
    }

    if( shadowStatus == SHADOW_STATUS_SUCCESS )
    {
        /* Extract thing name. */
        shadowStatus = extractThingName( & ( pTopic[ consumedTopicLength ] ),
                                         topicLength - consumedTopicLength,
                                         pThingName,
                                         pThingNameLength );
        if( shadowStatus == SHADOW_STATUS_SUCCESS )
        {
            consumedTopicLength += * pThingNameLength;

            /* If no more topic string is left to parse, fail. */
            if( consumedTopicLength >= topicLength )
            {
                shadowStatus = SHADOW_STATUS_SHADOW_MESSAGE_TYPE_PARSE_FAILED;
                LogDebug( ( "Not related to Shadow, shadow message type is not in pTopic %s, failed to parse shadow message type", pTopic ) );
            }
        }
        else
        {
            LogDebug( ( "Not related to Shadow, failed to parse thing name in pTopic %s", pTopic ) );
        }
    }

    if( shadowStatus == SHADOW_STATUS_SUCCESS )
    {
        /* Extract shadow message type. */
        shadowStatus = extractShadowMessageType( & ( pTopic[ consumedTopicLength ] ),
                                                 topicLength - consumedTopicLength,
                                                 pMessageType );
        if( shadowStatus != SHADOW_STATUS_SUCCESS )
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
    uint16_t offset = 0U, generatedTopicStringLength = 0U;
    ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;

    /* Lookup table for Shadow operation string. */
    static const char * const pTopicString[ SHADOW_TOPIC_STRING_TYPE_MAX_NUM ] =
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

    if( ( pTopicBuffer == NULL ) ||
        ( pThingName == NULL ) ||
        ( thingNameLength == 0U ) ||
        ( topicType >= SHADOW_TOPIC_STRING_TYPE_MAX_NUM ) ||
        ( pOutLength == NULL ) )
    {
        shadowStatus = SHADOW_STATUS_BAD_PARAMETER;
        LogError( ( "Invalid input parameters" ) );
    }
    else
    {
        generatedTopicStringLength = SHADOW_TOPIC_PREFIX_LENGTH +       /* Prefix ("$aws/things/"). */
                                     thingNameLength +                  /* Thing name. */
                                     pTopicStringLength[ topicType ];   /* Shadow operation. */

        if( bufferSize < generatedTopicStringLength )
        {
            shadowStatus = SHADOW_STATUS_BUFFER_TOO_SMALL;
            LogError( ( "Input bufferSize too small, bufferSize %d, required ", bufferSize, generatedTopicStringLength) );
        }
        else
        {
            /* Copy the Shadow topic prefix into the topic buffer. */
            ( void ) memcpy( ( void * ) pTopicBuffer,
                             ( const void * ) SHADOW_TOPIC_PREFIX_STRING,
                             ( size_t ) SHADOW_TOPIC_PREFIX_LENGTH );
            offset = ( uint16_t ) ( offset + SHADOW_TOPIC_PREFIX_LENGTH );

            /* Copy the Thing Name into the topic buffer. */
            ( void ) memcpy( ( void * ) & ( pTopicBuffer[ offset ] ),
                             ( const void * ) pThingName,
                             ( size_t ) thingNameLength );
            offset = ( uint16_t ) ( offset + thingNameLength );

            /* Copy the Shadow operation string into the topic buffer. */
            ( void ) memcpy( ( void * ) & ( pTopicBuffer[ offset ] ),
                             ( const void * ) pTopicString[ topicType ],
                             ( size_t ) pTopicStringLength[ topicType ] );

            /* Return the generated topic string length to the caller. */
            * pOutLength = generatedTopicStringLength;
        }
    }

    return shadowStatus;
}
/*-----------------------------------------------------------*/
