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
 * @file shadow.h
 * @brief User-facing Shadow functions, and parameter structs.
 */

#ifndef _SHADOW_H_
#define _SHADOW_H_

/* Standard includes. */
#include <stdint.h>
/* Include config file before other headers. */
#include "shadow_config.h"

/*--------------------------- Shadow types ---------------------------*/

/**
 * @brief Each of these values describes the type of a shadow message.
 *        https://docs.aws.amazon.com/iot/latest/developerguide/device-shadow-mqtt.html
 */
typedef enum ShadowMessageType
{
    ShadowMessageTypeGetAccepted = 0,
    ShadowMessageTypeGetRejected,
    ShadowMessageTypeDeleteAccepted,
    ShadowMessageTypeDeleteRejected,
    ShadowMessageTypeUpdateAccepted,
    ShadowMessageTypeUpdateRejected,
    ShadowMessageTypeUpdateDocuments,
    ShadowMessageTypeUpdateDelta,
    ShadowMessageTypeMaxNum
} ShadowMessageType_t;

/**
 * @brief Each of these values describes the type of a shadow topic string.
 *
 * These are used for topicType parameter of Shadow_GetTopicString() to tell it
 * what topic string to assemble.
 */
typedef enum ShadowTopicStringType
{
    ShadowTopicStringTypeGet = 0,
    ShadowTopicStringTypeGetAccepted,
    ShadowTopicStringTypeGetRejected,
    ShadowTopicStringTypeDelete,
    ShadowTopicStringTypeDeleteAccepted,
    ShadowTopicStringTypeDeleteRejected,
    ShadowTopicStringTypeUpdate,
    ShadowTopicStringTypeUpdateAccepted,
    ShadowTopicStringTypeUpdateRejected,
    ShadowTopicStringTypeUpdateDocuments,
    ShadowTopicStringTypeUpdateDelta,
    ShadowTopicStringTypeMaxNum
} ShadowTopicStringType_t;

/**
 * @brief Return codes from Shadow functions.
 */
typedef enum ShadowStatus
{
    SHADOW_SUCCESS = 0,                          /**< @brief Shadow function success. */
    SHADOW_FAIL,                                 /**< @brief Shadow function encountered error. */
    SHADOW_BAD_PARAMETER,                        /**< @brief Input parameter is invalid. */
    SHADOW_BUFFER_TOO_SMALL,                     /**< @brief The provided buffer is too small. */
    SHADOW_THINGNAME_PARSE_FAILED,               /**< @brief Could not parse the thing name. */
    SHADOW_SHADOW_MESSAGE_TYPE_PARSE_FAILED      /**< @brief Could not parse the shadow type. */
} ShadowStatus_t;

/*------------------------ Shadow library functions -------------------------*/

/**
 * @brief The common prefix of all Shadow MQTT topics
 *        from here https://docs.aws.amazon.com/iot/latest/developerguide/device-shadow-mqtt.html.
 */
#define SHADOW_PREFIX                                               "$aws/things/"

/**
 * @brief The length of #SHADOW_PREFIX.
 */
#define SHADOW_PREFIX_LENGTH                                        ( ( uint16_t ) ( sizeof( SHADOW_PREFIX ) - 1U ) )

/**
 * @brief The string representing a Shadow "DELETE" operation in a Shadow MQTT topic.
 */
#define SHADOW_OP_DELETE                                            "/shadow/delete"

/**
 * @brief The length of #SHADOW_OP_DELETE.
 */
#define SHADOW_OP_DELETE_LENGTH                                     ( ( uint16_t ) ( sizeof( SHADOW_OP_DELETE ) - 1U ) )

/**
 * @brief The string representing a Shadow "GET" operation in a Shadow MQTT topic.
 */
#define SHADOW_OP_GET                                               "/shadow/get"

/**
 * @brief The length of #SHADOW_OP_GET.
 */
#define SHADOW_OP_GET_LENGTH                                        ( ( uint16_t ) ( sizeof( SHADOW_OP_GET ) - 1U ) )

/**
 * @brief The string representing a Shadow "UPDATE" operation in a Shadow MQTT topic.
 */
#define SHADOW_OP_UPDATE                                            "/shadow/update"

/**
 * @brief The length of #SHADOW_OP_UPDATE.
 */
#define SHADOW_OP_UPDATE_LENGTH                                     ( ( uint16_t ) ( sizeof( SHADOW_OP_UPDATE ) - 1U ) )

/**
 * @brief The suffix for a Shadow operation "accepted" topic.
 */
#define SHADOW_SUFFIX_ACCEPTED                                      "/accepted"

/**
 * @brief The length of #SHADOW_SUFFIX_ACCEPTED.
 */
#define SHADOW_SUFFIX_ACCEPTED_LENGTH                               ( ( uint16_t ) ( sizeof( SHADOW_SUFFIX_ACCEPTED ) - 1U ) )

/**
 * @brief The suffix for a Shadow operation "rejected" topic.
 */
#define SHADOW_SUFFIX_REJECTED                                      "/rejected"

/**
 * @brief The length of #SHADOW_SUFFIX_REJECTED.
 */
#define SHADOW_SUFFIX_REJECTED_LENGTH                               ( ( uint16_t ) ( sizeof( SHADOW_SUFFIX_REJECTED ) - 1U ) )

/**
 * @brief The suffix for a Shadow "delta" topic.
 */
#define SHADOW_SUFFIX_DELTA                                         "/delta"

/**
 * @brief The length of #SHADOW_SUFFIX_DELTA.
 */
#define SHADOW_SUFFIX_DELTA_LENGTH                                  ( ( uint16_t ) ( sizeof( SHADOW_SUFFIX_DELTA ) - 1U ) )

/**
 * @brief The suffix for a Shadow "documents" topic.
 */
#define SHADOW_SUFFIX_DOCUMENTS                                     "/documents"

/**
 * @brief The length of #SHADOW_SUFFIX_DOCUMENTS.
 */
#define SHADOW_SUFFIX_DOCUMENTS_LENGTH                              ( ( uint16_t ) ( sizeof( SHADOW_SUFFIX_DOCUMENTS ) - 1U ) )

/**
 * @brief The suffix for a "null" suffix.
 */
#define SHADOW_SUFFIX_NULL

/**
 * @brief The length of null suffix.
 */
#define SHADOW_SUFFIX_NULL_LENGTH                                   ( 0U )

/**
 * @brief The maximum length of Thing Name.
 */
#define SHADOW_THINGNAME_LENGTH_MAX                                 ( 128U )

/**
 * @brief Compute shadow topic length.
 * 
 * The format of shadow topic strings is defined at https://docs.aws.amazon.com/iot/latest/developerguide/device-shadow-mqtt.html
 *
 * A shadow topic string takes one of the two forms:
 *     $aws/things/<thingName>/shadow/<operation>
 *     $aws/things/<thingName>/shadow/<operation>/<suffix>
 *
 * The <thingName>, <operation> and <suffix> segments correspond to the three input
 * parameters of this macro. The <suffix> part can be null.
 *
 * When thingName is known to be "myThing" at compile time, invoke the macro like this:
 * (In this case, the length is a constant at compile time.)
 *
 *     SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_DELTA_LENGTH, 7 )
 *
 * When thingName is only known at run time and held in a variable myThingName, invoke
 * the macro like this:
 *
 *     SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_DELTA_LENGTH,
 *                       strlen( ( const char * ) myThingName ) )
 *
 * @param[operationLen] Can be one of:
 *                          - SHADOW_OP_UPDATE_LENGTH
 *                          - SHADOW_OP_DELETE_LENGTH
 *                          - SHADOW_OP_GET_LENGTH
 * @param[suffixLen]    Can be one of:
 *                          - SHADOW_SUFFIX_NULL_LENGTH
 *                          - SHADOW_SUFFIX_ACCEPTED_LENGTH
 *                          - SHADOW_SUFFIX_REJECTED_LENGTH
 *                          - SHADOW_SUFFIX_DELTA_LENGTH
 *                          - SHADOW_SUFFIX_DOCUMENTS_LENGTH
 * @param[thingNameLength] Length of the thingName excluding the ending NULL.
 *
 * @return Length of the shadow topic in bytes.
 */
#define SHADOW_TOPIC_LENGTH( operationLength,  suffixLength,  thingNameLength )   \
                           ( operationLength + suffixLength + thingNameLength + SHADOW_PREFIX_LENGTH )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/update".
 */
#define SHADOW_TOPIC_LENGTH_UPDATE( thingNameLength )                       \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_NULL_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/update/accepted".
 */
#define SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( thingNameLength )              \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_ACCEPTED_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/update/rejected".
 */
#define SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( thingNameLength )              \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_REJECTED_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/update/documents".
 */
#define SHADOW_TOPIC_LENGTH_UPDATE_DOCUMENTS( thingNameLength )             \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_DOCUMENTS_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/update/delta".
 */
#define SHADOW_TOPIC_LENGTH_UPDATE_DELTA( thingNameLength )                 \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_DELTA_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/get".
 */
#define SHADOW_TOPIC_LENGTH_GET( thingNameLength )                          \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_GET_LENGTH, SHADOW_SUFFIX_NULL_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/get/accepted".
 */
#define SHADOW_TOPIC_LENGTH_GET_ACCEPTED( thingNameLength )                 \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_GET_LENGTH, SHADOW_SUFFIX_ACCEPTED_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/get/rejected".
 */
#define SHADOW_TOPIC_LENGTH_GET_REJECTED( thingNameLength )                 \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_GET_LENGTH, SHADOW_SUFFIX_REJECTED_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/delete".
 */
#define SHADOW_TOPIC_LENGTH_DELETE( thingNameLength )                       \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_DELETE_LENGTH, SHADOW_SUFFIX_NULL_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/delete/accepted".
 */
#define SHADOW_TOPIC_LENGTH_DELETE_ACCEPTED( thingNameLength )              \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_DELETE_LENGTH, SHADOW_SUFFIX_ACCEPTED_LENGTH, thingNameLength )

/**
 * @brief Compute the length of shadow topic "$aws/things/<thingName>/shadow/delete/rejected".
 */
#define SHADOW_TOPIC_LENGTH_DELETE_REJECTED( thingNameLength )              \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_DELETE_LENGTH, SHADOW_SUFFIX_REJECTED_LENGTH, thingNameLength )

/**
 * @brief Compute the length of the longest shadow topic.
 */
#define SHADOW_TOPIC_LENGTH_MAX( thingNameLength )                          \
        SHADOW_TOPIC_LENGTH( SHADOW_OP_UPDATE_LENGTH, SHADOW_SUFFIX_DOCUMENTS_LENGTH, thingNameLength )

/**
 * @brief Assemble constant shadow topic strings when Thing Name is known at compile time.
 *
 * When thingName is known to be "myThing" at compile time, invoke the macro like this:
 *
 *     SHADOW_TOPIC_STRING( SHADOW_OP_UPDATE, SHADOW_SUFFIX_DELTA, "myThing" )
 *
 * When thingName is only known at run time, do not use this macro. Use the
 * Shadow_GetTopicString() function instead.
 *
 * @param[operation] Can be one of:
 *                       - SHADOW_OP_UPDATE
 *                       - SHADOW_OP_DELETE
 *                       - SHADOW_OP_GET
 * @param[suffix]    Can be one of: 
 *                       - SHADOW_SUFFIX_NULL
 *                       - SHADOW_SUFFIX_ACCEPTED
 *                       - SHADOW_SUFFIX_REJECTED
 *                       - SHADOW_SUFFIX_DELTA
 *                       - SHADOW_SUFFIX_DOCUMENTS
 *                          
 * @param[thingName] Thing Name.
 *
 * @return Topic string.
 */                       
#define SHADOW_TOPIC_STRING( thingName, operation, suffix )     \
                           ( SHADOW_PREFIX thingName operation suffix )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/update".
 */
#define SHADOW_TOPIC_STRING_UPDATE( thingName )                 \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_UPDATE, SHADOW_SUFFIX_NULL )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/update/accepted".
 */
#define SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( thingName )        \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_UPDATE, SHADOW_SUFFIX_ACCEPTED )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/update/rejected".
 */
#define SHADOW_TOPIC_STRING_UPDATE_REJECTED( thingName )        \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_UPDATE, SHADOW_SUFFIX_REJECTED )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/update/documents".
 */
#define SHADOW_TOPIC_STRING_UPDATE_DOCUMENTS( thingName )        \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_UPDATE, SHADOW_SUFFIX_DOCUMENTS )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/update/delta".
 */
#define SHADOW_TOPIC_STRING_UPDATE_DELTA( thingName )           \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_UPDATE, SHADOW_SUFFIX_DELTA )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/get".
 */
#define SHADOW_TOPIC_STRING_GET( thingName )                    \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_GET, SHADOW_SUFFIX_NULL )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/get/accepted".
 */
#define SHADOW_TOPIC_STRING_GET_ACCEPTED( thingName )           \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_GET, SHADOW_SUFFIX_ACCEPTED )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/get/rejected".
 */
#define SHADOW_TOPIC_STRING_GET_REJECTED( thingName )           \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_GET, SHADOW_SUFFIX_REJECTED )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/delete".
 */
#define SHADOW_TOPIC_STRING_DELETE( thingName )                 \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_DELETE, SHADOW_SUFFIX_NULL )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/delete/accepted".
 */
#define SHADOW_TOPIC_STRING_DELETE_ACCEPTED( thingName )        \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_DELETE, SHADOW_SUFFIX_ACCEPTED )

/**
 * @brief Assemble shadow topic string "$aws/things/<thingName>/shadow/delete/rejected".
 */
#define SHADOW_TOPIC_STRING_DELETE_REJECTED( thingName )        \
        SHADOW_TOPIC_STRING( thingName, SHADOW_OP_DELETE, SHADOW_SUFFIX_REJECTED )

/**
 * @brief Assemble shadow topic strings when Thing Name is only known at run time.
 *
 * @param[in]  topicType Indicates what topic will be written into the buffer pointed to by pTopicBuffer.
 *             can be one of:
 *                 - ShadowTopicStringTypeGet
 *                 - ShadowTopicStringTypeGetAccepted
 *                 - ShadowTopicStringTypeGetRejected
 *                 - ShadowTopicStringTypeDelete
 *                 - ShadowTopicStringTypeDeleteAccepted
 *                 - ShadowTopicStringTypeDeleteRejected
 *                 - ShadowTopicStringTypeUpdate
 *                 - ShadowTopicStringTypeUpdateAccepted
 *                 - ShadowTopicStringTypeUpdateRejected
 *                 - ShadowTopicStringTypeUpdateDocuments
 *                 - ShadowTopicStringTypeUpdateDelta
 * @param[in]  pThingName Thing Name string. No need to be null terminated. Must not be NULL.
 * @param[in]  thingNameLength Length of Thing Name string pointed to by pThingName. Must not be zero.
 * @param[out] pTopicBuffer Pointer to buffer for returning the topic string.
 *             Caller is responsible for supplying memory pointed to by pTopicBuffer.
 *             This function does not fill in the terminating null character. The app
 *             can supply a buffer that does not have space for holding the null character.
 * @param[in]  bufferSize Length of pTopicBuffer. This function will return error if
 *             bufferSize is less than the length of the assembled topic string.
 * @param[out] pOutLength Pointer to caller-supplied memory for returning the length of the topic string.
 * @return     One of the following:
 *             - SHADOW_SUCCESS if successful.
 *             - An error code if failed to assemble.
 */
ShadowStatus_t Shadow_GetTopicString( ShadowTopicStringType_t topicType,
                                      const char * pThingName,
                                      uint8_t thingNameLength,
                                      char * pTopicBuffer,
                                      uint16_t bufferSize,
                                      uint16_t * pOutLength );

/**
 * @brief Given the topic string of an incoming message, determine whether it is 
 *        related to a device shadow; if it is, return information about the type of
 *        device shadow message, and a pointer to the Thing Name inside of the topic string.
 *
 * @note When this function returns, the pointer pThingName points at the first character
 *       of the <thingName> segment inside of the topic string.
 *       Caller is responsible for keeping the memory holding the topic strings around.
 *
 * @param[in]  pTopic Pointer to the MQTT topic string. Does not have to be null-terminated.
 * @param[in]  topicLength Length of the MQTT topic string.
 * @param[out] pMessageType Pointer to call-supplied memory for returning the type of the shadow message.
 * @param[out] pThingName Points to the 1st character of Thing Name inside of the topic string.
 * @param[out] pThingNameLength Pointer to caller-supplied memory for returning the length of the Thing Name.
 * @return     One of the following:
 *             - SHADOW_SUCCESS if the message is related to a device shadow;
 *             - An error code if the message is not related to a device shadow,
 *               if any input parameter is invalid, or if the function fails to
 *               parse the topic string.
 */
ShadowStatus_t Shadow_MatchTopic( const char * pTopic,
                                  uint16_t topicLength,
                                  ShadowMessageType_t * pMessageType,
                                  const char ** pThingName,
                                  uint16_t * pThingNameLength );

#endif /* ifndef _SHADOW_H_ */
