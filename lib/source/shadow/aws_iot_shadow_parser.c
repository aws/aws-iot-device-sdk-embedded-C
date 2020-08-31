/*
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_shadow_parser.c
 * @brief Implements JSON parsing functions of the Shadow library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Shadow internal include. */
#include "private/aws_iot_shadow_internal.h"

/* Error handling include. */
#include "private/iot_error.h"

/* JSON utilities include. */
#include "iot_json_utils.h"

/*-----------------------------------------------------------*/

/**
 * @brief The JSON key for the error code in a Shadow error document.
 */
#define ERROR_DOCUMENT_CODE_KEY              "code"

/**
 * @brief The length of #ERROR_DOCUMENT_CODE_KEY.
 */
#define ERROR_DOCUMENT_CODE_KEY_LENGTH       ( sizeof( ERROR_DOCUMENT_CODE_KEY ) - 1 )

/**
 * @brief The JSON key for the error message in a Shadow error document.
 */
#define ERROR_DOCUMENT_MESSAGE_KEY           "message"

/**
 * @brief The length of #ERROR_DOCUMENT_MESSAGE_KEY.
 */
#define ERROR_DOCUMENT_MESSAGE_KEY_LENGTH    ( sizeof( ERROR_DOCUMENT_MESSAGE_KEY ) - 1 )

/**
 * @brief The minimum possible length of a Shadow topic name, per the Shadow
 * spec.
 */
#define MINIMUM_SHADOW_TOPIC_NAME_LENGTH                                  \
    ( SHADOW_TOPIC_PREFIX_LENGTH +                                        \
      ( uint16_t ) sizeof( SHADOW_GET_OPERATION_STRING ) +                \
      ( AWS_IOT_ACCEPTED_SUFFIX_LENGTH < AWS_IOT_REJECTED_SUFFIX_LENGTH ? \
        AWS_IOT_ACCEPTED_SUFFIX_LENGTH :                                  \
        AWS_IOT_REJECTED_SUFFIX_LENGTH ) )

/*-----------------------------------------------------------*/

/**
 * @brief Converts a `unsigned long` to an `AwsIotShadowError_t`.
 *
 * @param[in] code A value between 400 and 500 to convert.
 *
 * @return A corresponding #AwsIotShadowError_t; #AWS_IOT_SHADOW_BAD_RESPONSE
 * if `code` is unknown.
 */
static AwsIotShadowError_t _codeToShadowStatus( uint32_t code );

/*-----------------------------------------------------------*/

static AwsIotShadowError_t _codeToShadowStatus( uint32_t code )
{
    AwsIotShadowError_t errorCode = AWS_IOT_SHADOW_STATUS_PENDING;

    /* Convert the Shadow response code to an AwsIotShadowError_t. */
    switch( code )
    {
        case 400UL:
            errorCode = AWS_IOT_SHADOW_BAD_REQUEST;
            break;

        case 401UL:
            errorCode = AWS_IOT_SHADOW_UNAUTHORIZED;
            break;

        case 403UL:
            errorCode = AWS_IOT_SHADOW_FORBIDDEN;
            break;

        case 404UL:
            errorCode = AWS_IOT_SHADOW_NOT_FOUND;
            break;

        case 409UL:
            errorCode = AWS_IOT_SHADOW_CONFLICT;
            break;

        case 413UL:
            errorCode = AWS_IOT_SHADOW_TOO_LARGE;
            break;

        case 415UL:
            errorCode = AWS_IOT_SHADOW_UNSUPPORTED;
            break;

        case 429UL:
            errorCode = AWS_IOT_SHADOW_TOO_MANY_REQUESTS;
            break;

        case 500UL:
            errorCode = AWS_IOT_SHADOW_SERVER_ERROR;
            break;

        default:
            errorCode = AWS_IOT_SHADOW_BAD_RESPONSE;
            break;
    }

    return errorCode;
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t _AwsIotShadow_ParseErrorDocument( const char * pErrorDocument,
                                                      size_t errorDocumentLength )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_STATUS_PENDING );
    const char * pCode = NULL, * pMessage = NULL;
    size_t codeLength = 0, messageLength = 0;
    uint32_t code = 0;

    /* Parse the code from the error document. */
    if( IotJsonUtils_FindJsonValue( pErrorDocument,
                                    errorDocumentLength,
                                    ERROR_DOCUMENT_CODE_KEY,
                                    ERROR_DOCUMENT_CODE_KEY_LENGTH,
                                    &pCode,
                                    &codeLength ) == false )
    {
        /* Error parsing JSON document, or no "code" key was found. */
        IotLogWarn( "Failed to parse code from error document.\n%.*s",
                    errorDocumentLength,
                    pErrorDocument );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_RESPONSE );
    }

    /* Code must be in error document. */
    AwsIotShadow_Assert( ( pCode > pErrorDocument ) &&
                         ( pCode + codeLength < pErrorDocument + errorDocumentLength ) );

    /* Convert the code to an unsigned integer value. */
    code = ( uint32_t ) strtoul( pCode, NULL, 10 );

    /* Parse the error message and print it. An error document must always contain
     * a message. */
    if( IotJsonUtils_FindJsonValue( pErrorDocument,
                                    errorDocumentLength,
                                    ERROR_DOCUMENT_MESSAGE_KEY,
                                    ERROR_DOCUMENT_MESSAGE_KEY_LENGTH,
                                    &pMessage,
                                    &messageLength ) == true )
    {
        IotLogWarn( "Code %lu: %.*s.",
                    code,
                    messageLength,
                    pMessage );
    }
    else
    {
        IotLogWarn( "Code %lu; failed to parse message from error document.\n%.*s",
                    code,
                    errorDocumentLength,
                    pErrorDocument );

        /* An error document must contain a message; if it does not, then it is invalid. */
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_RESPONSE );
    }

    /* Convert a successfully parsed JSON code to a Shadow status. */
    status = _codeToShadowStatus( code );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t _AwsIotShadow_ParseThingName( const char * pTopicName,
                                                  uint16_t topicNameLength,
                                                  const char ** pThingName,
                                                  size_t * pThingNameLength )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_SUCCESS );
    const char * pThingNameStart = NULL;
    size_t thingNameLength = 0;

    /* Check that the topic name length exceeds the minimum possible length. */
    if( topicNameLength < MINIMUM_SHADOW_TOPIC_NAME_LENGTH )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_RESPONSE );
    }

    /* All Shadow topic names must start with the same prefix. */
    if( strncmp( SHADOW_TOPIC_PREFIX,
                 pTopicName,
                 SHADOW_TOPIC_PREFIX_LENGTH ) != 0 )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_RESPONSE );
    }

    /* The Thing Name starts immediately after the topic prefix. */
    pThingNameStart = pTopicName + SHADOW_TOPIC_PREFIX_LENGTH;

    /* Calculate the length of the Thing Name. */
    while( ( thingNameLength + SHADOW_TOPIC_PREFIX_LENGTH < ( size_t ) topicNameLength ) &&
           ( pThingNameStart[ thingNameLength ] != '/' ) )
    {
        thingNameLength++;
    }

    /* The end of the topic name was reached without finding a '/'. The topic
     * name is invalid. */
    if( thingNameLength + SHADOW_TOPIC_PREFIX_LENGTH >= ( size_t ) topicNameLength )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_RESPONSE );
    }

    /* Set the output parameters. */
    *pThingName = pThingNameStart;
    *pThingNameLength = thingNameLength;

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/
