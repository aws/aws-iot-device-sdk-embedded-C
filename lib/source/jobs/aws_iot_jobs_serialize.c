/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_jobs_serialize.c
 * @brief Implements functions that generate and parse Jobs JSON documents.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/* Error handling include. */
#include "private/iot_error.h"

/**
 * @brief Minimum length of a Jobs request.
 *
 * At the very least, the request will contain: {"clientToken":""}
 */
#define MINIMUM_REQUEST_LENGTH              ( AWS_IOT_CLIENT_TOKEN_KEY_LENGTH + 7 )

/**
 * @brief The length of client tokens generated by this library.
 */
#define CLIENT_TOKEN_AUTOGENERATE_LENGTH    ( 8 )

/**
 * @brief JSON key representing Jobs status details.
 */
#define STATUS_DETAILS_KEY                  "statusDetails"

/**
 * @brief Length of #STATUS_DETAILS_KEY.
 */
#define STATUS_DETAILS_KEY_LENGTH           ( sizeof( STATUS_DETAILS_KEY ) - 1 )

/**
 * @brief JSON key representing Jobs step timeout.
 */
#define STEP_TIMEOUT_KEY                    "stepTimeoutInMinutes"

/**
 * @brief Length of #STEP_TIMEOUT_KEY.
 */
#define STEP_TIMEOUT_KEY_LENGTH             ( sizeof( STEP_TIMEOUT_KEY ) - 1 )

/**
 * @brief JSON key representing the "include Job document" flag.
 */
#define INCLUDE_JOB_DOCUMENT_KEY            "includeJobDocument"

/**
 * @brief Length of #INCLUDE_JOB_DOCUMENT_KEY.
 */
#define INCLUDE_JOB_DOCUMENT_KEY_LENGTH     ( sizeof( INCLUDE_JOB_DOCUMENT_KEY ) - 1 )

/**
 * @brief JSON key representing the Jobs execution number.
 */
#define EXECUTION_NUMBER_KEY                "executionNumber"

/**
 * @brief Length of #EXECUTION_NUMBER_KEY.
 */
#define EXECUTION_NUMBER_KEY_LENGTH         ( sizeof( EXECUTION_NUMBER_KEY ) - 1 )

/**
 * @brief Maximum length of the execution number when represented as a string.
 *
 * The execution number is a 32-bit integer. This can be represented in 10 digits,
 * plus 1 for a possible negative sign, plus a NULL-terminator.
 */
#define EXECUTION_NUMBER_STRING_LENGTH      ( 12 )

/**
 * @brief Append a string to a buffer.
 *
 * Also updates `copyOffset` with `stringLength`.
 *
 * @param[in] pBuffer Start of a buffer.
 * @param[in] copyOffset Offset in `pBuffer` where `pString` will be placed.
 * @param[in] pString The string to append.
 * @param[in] stringLength Length of `pString`.
 */
#define APPEND_STRING( pBuffer, copyOffset, pString, stringLength ) \
    ( void ) memcpy( pBuffer + copyOffset, pString, stringLength ); \
    copyOffset += ( size_t ) stringLength;

/*-----------------------------------------------------------*/

/**
 * @brief Place a client token in the given buffer.
 *
 * @param[in] pBuffer The buffer where the client token is placed.
 * @param[in] copyOffset Offset in `pBuffer` where client token is placed.
 * @param[in] pRequestInfo Contains information on a client token to place.
 * @param[out] pOperation Location and length of client token are written here.
 *
 * @warning This function does not check the length of `pBuffer`! Any provided
 * buffer must be large enough to accommodate #CLIENT_TOKEN_AUTOGENERATE_LENGTH
 * characters.
 *
 * @return A value of `copyOffset` after the client token.
 */
static size_t _appendClientToken( char * pBuffer,
                                  size_t copyOffset,
                                  const AwsIotJobsRequestInfo_t * pRequestInfo,
                                  _jobsOperation_t * pOperation );

/**
 * @brief Generates a request JSON for a GET PENDING operation.
 *
 * @param[in] pRequestInfo Common Jobs request parameters.
 * @param[in] pOperation Operation associated with the Jobs request.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_NO_MEMORY
 */
static AwsIotJobsError_t _generateGetPendingRequest( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                     _jobsOperation_t * pOperation );

/**
 * @brief Generates a request JSON for a START NEXT operation.
 *
 * @param[in] pRequestInfo Common Jobs request parameters.
 * @param[in] pUpdateInfo Jobs update parameters.
 * @param[in] pOperation Operation associated with the Jobs request.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_NO_MEMORY
 */
static AwsIotJobsError_t _generateStartNextRequest( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                    const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                                    _jobsOperation_t * pOperation );

/**
 * @brief Generates a request JSON for a DESCRIBE operation.
 *
 * @param[in] pRequestInfo Common jobs request parameters.
 * @param[in] executionNumber Job execution number to include in request.
 * @param[in] includeJobDocument Whether the response should include the Job document.
 * @param[in] pOperation Operation associated with the Jobs request.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_NO_MEMORY.
 */
static AwsIotJobsError_t _generateDescribeRequest( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                   int32_t executionNumber,
                                                   bool includeJobDocument,
                                                   _jobsOperation_t * pOperation );

/*-----------------------------------------------------------*/

static size_t _appendClientToken( char * pBuffer,
                                  size_t copyOffset,
                                  const AwsIotJobsRequestInfo_t * pRequestInfo,
                                  _jobsOperation_t * pOperation )
{
    int clientTokenLength = 0;
    uint32_t clientToken = 0;

    /* Place the client token key in the buffer. */
    APPEND_STRING( pBuffer,
                   copyOffset,
                   AWS_IOT_CLIENT_TOKEN_KEY,
                   AWS_IOT_CLIENT_TOKEN_KEY_LENGTH );
    APPEND_STRING( pBuffer, copyOffset, "\":\"", 3 );

    /* Set the pointer to the client token. */
    pOperation->pClientToken = pBuffer + copyOffset - 1;

    if( pRequestInfo->pClientToken == AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE )
    {
        /* Take the address of the given buffer, truncated to 8 characters. This
         * provides a client token that is very likely to be unique while in use. */
        clientToken = ( uint32_t ) ( ( uint64_t ) pBuffer % 100000000ULL );

        clientTokenLength = snprintf( pBuffer + copyOffset,
                                      CLIENT_TOKEN_AUTOGENERATE_LENGTH + 1,
                                      "%08u", clientToken );
        AwsIotJobs_Assert( clientTokenLength == CLIENT_TOKEN_AUTOGENERATE_LENGTH );

        copyOffset += ( size_t ) clientTokenLength;
        pOperation->clientTokenLength = CLIENT_TOKEN_AUTOGENERATE_LENGTH + 2;
    }
    else
    {
        APPEND_STRING( pBuffer,
                       copyOffset,
                       pRequestInfo->pClientToken,
                       pRequestInfo->clientTokenLength );

        pOperation->clientTokenLength = pRequestInfo->clientTokenLength + 2;
    }

    return copyOffset;
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _generateGetPendingRequest( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                     _jobsOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    char * pJobsRequest = NULL;
    size_t copyOffset = 0;
    size_t requestLength = MINIMUM_REQUEST_LENGTH;

    /* Add the length of the client token. */
    if( pRequestInfo->pClientToken != AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE )
    {
        AwsIotJobs_Assert( pRequestInfo->clientTokenLength > 0 );

        requestLength += pRequestInfo->clientTokenLength;
    }
    else
    {
        requestLength += CLIENT_TOKEN_AUTOGENERATE_LENGTH;
    }

    /* Allocate memory for the request JSON. */
    pJobsRequest = AwsIotJobs_MallocString( requestLength );

    if( pJobsRequest == NULL )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
    }

    /* Clear the request JSON. */
    ( void ) memset( pJobsRequest, 0x00, requestLength );

    /* Construct the request JSON, which consists of just a clientToken key. */
    APPEND_STRING( pJobsRequest, copyOffset, "{\"", 2 );
    copyOffset = _appendClientToken( pJobsRequest, copyOffset, pRequestInfo, pOperation );
    APPEND_STRING( pJobsRequest, copyOffset, "\"}", 2 );

    /* Set the output parameters. */
    pOperation->pJobsRequest = pJobsRequest;
    pOperation->jobsRequestLength = requestLength;

    /* Ensure offsets are valid. */
    AwsIotJobs_Assert( copyOffset == requestLength );
    AwsIotJobs_Assert( pOperation->pClientToken > pOperation->pJobsRequest );
    AwsIotJobs_Assert( pOperation->pClientToken <
                       pOperation->pJobsRequest + pOperation->jobsRequestLength );

    IotLogDebug( "Jobs GET PENDING request: %.*s",
                 pOperation->jobsRequestLength,
                 pOperation->pJobsRequest );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _generateStartNextRequest( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                    const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                                    _jobsOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    char * pJobsRequest = NULL;
    size_t copyOffset = 0;
    size_t requestLength = MINIMUM_REQUEST_LENGTH;
    char pStepTimeout[ 6 ] = { 0 };
    int stepTimeoutLength = 0;

    /* Add the length of status details if provided. */
    if( pUpdateInfo->pStatusDetails != AWS_IOT_JOBS_NO_STATUS_DETAILS )
    {
        /* Add 4 for the 2 quotes, colon, and comma. */
        requestLength += STATUS_DETAILS_KEY_LENGTH + 4;
        requestLength += pUpdateInfo->statusDetailsLength;
    }

    /* Calculate the length of the step timeout. Add 4 for the 2 quotes, colon, and comma. */
    requestLength += STEP_TIMEOUT_KEY_LENGTH + 4;

    if( pUpdateInfo->stepTimeoutInMinutes != AWS_IOT_JOBS_NO_TIMEOUT )
    {
        /* Convert the step timeout to a string. */
        stepTimeoutLength = snprintf( pStepTimeout, 6, "%d", pUpdateInfo->stepTimeoutInMinutes );
        AwsIotJobs_Assert( stepTimeoutLength > 0 );
        AwsIotJobs_Assert( stepTimeoutLength < 6 );
    }
    else
    {
        /* Step timeout will be set to -1. */
        pStepTimeout[ 0 ] = '-';
        pStepTimeout[ 1 ] = '1';
        stepTimeoutLength = 2;
    }

    requestLength += ( size_t ) stepTimeoutLength;

    /* Add the length of the client token. */
    if( pRequestInfo->pClientToken != AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE )
    {
        AwsIotJobs_Assert( pRequestInfo->clientTokenLength > 0 );

        requestLength += pRequestInfo->clientTokenLength;
    }
    else
    {
        requestLength += CLIENT_TOKEN_AUTOGENERATE_LENGTH;
    }

    /* Allocate memory for the request JSON. */
    pJobsRequest = AwsIotJobs_MallocString( requestLength );

    if( pJobsRequest == NULL )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
    }

    /* Clear the request JSON. */
    ( void ) memset( pJobsRequest, 0x00, requestLength );

    /* Construct the request JSON. */
    APPEND_STRING( pJobsRequest, copyOffset, "{\"", 2 );

    /* Add status details if present. */
    if( pUpdateInfo->pStatusDetails != AWS_IOT_JOBS_NO_STATUS_DETAILS )
    {
        APPEND_STRING( pJobsRequest, copyOffset, STATUS_DETAILS_KEY, STATUS_DETAILS_KEY_LENGTH );
        APPEND_STRING( pJobsRequest, copyOffset, "\":", 2 );
        APPEND_STRING( pJobsRequest,
                       copyOffset,
                       pUpdateInfo->pStatusDetails,
                       pUpdateInfo->statusDetailsLength );
        APPEND_STRING( pJobsRequest, copyOffset, ",\"", 2 );
    }

    /* Add step timeout. */
    APPEND_STRING( pJobsRequest,
                   copyOffset,
                   STEP_TIMEOUT_KEY,
                   STEP_TIMEOUT_KEY_LENGTH );
    APPEND_STRING( pJobsRequest, copyOffset, "\":", 2 );
    APPEND_STRING( pJobsRequest, copyOffset, pStepTimeout, stepTimeoutLength );
    APPEND_STRING( pJobsRequest, copyOffset, ",\"", 2 );

    /* Add client token. */
    copyOffset = _appendClientToken( pJobsRequest, copyOffset, pRequestInfo, pOperation );

    APPEND_STRING( pJobsRequest, copyOffset, "\"}", 2 );

    /* Set the output parameters. */
    pOperation->pJobsRequest = pJobsRequest;
    pOperation->jobsRequestLength = requestLength;

    /* Ensure offsets are valid. */
    AwsIotJobs_Assert( copyOffset == requestLength );
    AwsIotJobs_Assert( pOperation->pClientToken > pOperation->pJobsRequest );
    AwsIotJobs_Assert( pOperation->pClientToken <
                       pOperation->pJobsRequest + pOperation->jobsRequestLength );

    IotLogDebug( "Jobs START NEXT request: %.*s",
                 pOperation->jobsRequestLength,
                 pOperation->pJobsRequest );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _generateDescribeRequest( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                   int32_t executionNumber,
                                                   bool includeJobDocument,
                                                   _jobsOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    char * pJobsRequest = NULL;
    size_t copyOffset = 0;
    size_t requestLength = MINIMUM_REQUEST_LENGTH;
    char pExecutionNumber[ EXECUTION_NUMBER_STRING_LENGTH ] = { 0 };
    int executionNumberLength = 0;

    /* Add the "include job document" flag if false. The default value is true,
     * so the flag is not needed if true. */
    if( includeJobDocument == false )
    {
        /* Add the length of "includeJobDocument" plus 4 for 2 quotes, a colon,
         * and a comma. */
        requestLength += INCLUDE_JOB_DOCUMENT_KEY_LENGTH + 4;

        /* Add the length of "false". */
        requestLength += 5;
    }

    /* Add the length of the execution number if present. */
    if( executionNumber != AWS_IOT_JOBS_NO_EXECUTION_NUMBER )
    {
        /* Convert the execution number to a string. */
        executionNumberLength = snprintf( pExecutionNumber,
                                          EXECUTION_NUMBER_STRING_LENGTH,
                                          "%d",
                                          executionNumber );
        AwsIotJobs_Assert( executionNumberLength > 0 );
        AwsIotJobs_Assert( executionNumberLength < EXECUTION_NUMBER_STRING_LENGTH );

        requestLength += EXECUTION_NUMBER_KEY_LENGTH + 4;
        requestLength += ( size_t ) executionNumberLength;
    }

    /* Add the length of the client token. */
    if( pRequestInfo->pClientToken != AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE )
    {
        AwsIotJobs_Assert( pRequestInfo->clientTokenLength > 0 );

        requestLength += pRequestInfo->clientTokenLength;
    }
    else
    {
        requestLength += CLIENT_TOKEN_AUTOGENERATE_LENGTH;
    }

    /* Allocate memory for the request JSON. */
    pJobsRequest = AwsIotJobs_MallocString( requestLength );

    if( pJobsRequest == NULL )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
    }

    /* Clear the request JSON. */
    ( void ) memset( pJobsRequest, 0x00, requestLength );

    /* Construct the request JSON. */
    APPEND_STRING( pJobsRequest, copyOffset, "{\"", 2 );

    /* Add the "include job document" flag if false. */
    if( includeJobDocument == false )
    {
        APPEND_STRING( pJobsRequest,
                       copyOffset,
                       INCLUDE_JOB_DOCUMENT_KEY,
                       INCLUDE_JOB_DOCUMENT_KEY_LENGTH );
        APPEND_STRING( pJobsRequest, copyOffset, "\":false,\"", 9 );
    }

    /* Add the length of the execution number if present. */
    if( executionNumber != AWS_IOT_JOBS_NO_EXECUTION_NUMBER )
    {
        APPEND_STRING( pJobsRequest,
                       copyOffset,
                       EXECUTION_NUMBER_KEY,
                       EXECUTION_NUMBER_KEY_LENGTH );
        APPEND_STRING( pJobsRequest,
                       copyOffset,
                       "\":",
                       2 );
        APPEND_STRING( pJobsRequest,
                       copyOffset,
                       pExecutionNumber,
                       executionNumberLength );
        APPEND_STRING( pJobsRequest, copyOffset, ",\"", 2 );
    }

    /* Add client token. */
    copyOffset = _appendClientToken( pJobsRequest, copyOffset, pRequestInfo, pOperation );

    APPEND_STRING( pJobsRequest, copyOffset, "\"}", 2 );

    /* Set the output parameters. */
    pOperation->pJobsRequest = pJobsRequest;
    pOperation->jobsRequestLength = requestLength;

    /* Ensure offsets are valid. */
    AwsIotJobs_Assert( copyOffset == requestLength );
    AwsIotJobs_Assert( pOperation->pClientToken > pOperation->pJobsRequest );
    AwsIotJobs_Assert( pOperation->pClientToken <
                       pOperation->pJobsRequest + pOperation->jobsRequestLength );

    IotLogDebug( "Jobs DESCRIBE request: %.*s",
                 pOperation->jobsRequestLength,
                 pOperation->pJobsRequest );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t _AwsIotJobs_GenerateJsonRequest( _jobsOperationType_t type,
                                                   const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                   const _jsonRequestContents_t * pRequestContents,
                                                   _jobsOperation_t * pOperation )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;

    /* Generate request based on the Job operation type. */
    switch( type )
    {
        case JOBS_GET_PENDING:
            status = _generateGetPendingRequest( pRequestInfo, pOperation );
            break;

        case JOBS_START_NEXT:
            status = _generateStartNextRequest( pRequestInfo,
                                                pRequestContents->pUpdateInfo,
                                                pOperation );
            break;

        case JOBS_DESCRIBE:
            status = _generateDescribeRequest( pRequestInfo,
                                               pRequestContents->describe.executionNumber,
                                               pRequestContents->describe.includeJobDocument,
                                               pOperation );
            break;

        default:
            /* The only remaining valid type is UPDATE. */
            AwsIotJobs_Assert( type == JOBS_UPDATE );
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/
