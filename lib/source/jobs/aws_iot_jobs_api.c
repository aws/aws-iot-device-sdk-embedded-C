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
 * @file aws_iot_jobs_api.c
 * @brief Implements the user-facing functions of the Jobs library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/* Error handling include. */
#include "private/iot_error.h"

/* Validate Jobs configuration settings. */
#if AWS_IOT_JOBS_ENABLE_ASSERTS != 0 && AWS_IOT_JOBS_ENABLE_ASSERTS != 1
    #error "AWS_IOT_JOBS_ENABLE_ASSERTS must be 0 or 1."
#endif
#if AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS <= 0
    #error "AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS cannot be 0 or negative."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Validate the #AwsIotJobsRequestInfo_t passed to a Jobs API function.
 *
 * @param[in] type The Jobs API function type.
 * @param[in] pRequestInfo The request info passed to a Jobs API function.
 * @param[in] flags Flags used by the Jobs API function.
 * @param[in] pCallbackInfo The callback info passed with the request info.
 * @param[in] pOperation Operation reference pointer passed to a Jobs API function.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_BAD_PARAMETER.
 */
static AwsIotJobsError_t _validateRequestInfo( _jobsOperationType_t type,
                                               const AwsIotJobsRequestInfo_t * pRequestInfo,
                                               uint32_t flags,
                                               const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                               const AwsIotJobsOperation_t * pOperation );

/**
 * @brief Validate the #AwsIotJobsUpdateInfo_t passed to a Jobs API function.
 *
 * @param[in] type The Jobs API function type.
 * @param[in] pUpdateInfo The update info passed to a Jobs API function.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_BAD_PARAMETER.
 */
static AwsIotJobsError_t _validateUpdateInfo( _jobsOperationType_t type,
                                              const AwsIotJobsUpdateInfo_t * pUpdateInfo );

/*-----------------------------------------------------------*/

/**
 * @brief Timeout used for MQTT operations.
 */
uint32_t _AwsIotJobsMqttTimeoutMs = AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS;

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief Printable names for the Jobs callbacks.
 */
    const char * const _pAwsIotJobsCallbackNames[] =
    {
        "NOTIFY PENDING",
        "NOTIFY NEXT"
    };
#endif

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _validateRequestInfo( _jobsOperationType_t type,
                                               const AwsIotJobsRequestInfo_t * pRequestInfo,
                                               uint32_t flags,
                                               const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                               const AwsIotJobsOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );

    /* Check that the given MQTT connection is valid. */
    if( pRequestInfo->mqttConnection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized for Jobs %s.",
                     _pAwsIotJobsOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check Thing Name. */
    if( AwsIot_ValidateThingName( pRequestInfo->pThingName,
                                  pRequestInfo->thingNameLength ) == false )
    {
        IotLogError( "Thing Name is not valid for Jobs %s.",
                     _pAwsIotJobsOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Checks for waitable operations. */
    if( ( flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == AWS_IOT_JOBS_FLAG_WAITABLE )
    {
        if( pOperation == NULL )
        {
            IotLogError( "Reference must be provided for a waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->mallocResponse == NULL )
        {
            IotLogError( "Memory allocation function must be set for waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pCallbackInfo != NULL )
        {
            IotLogError( "Callback should not be set for a waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check that a callback function is set. */
    if( pCallbackInfo != NULL )
    {
        if( pCallbackInfo->function == NULL )
        {
            IotLogError( "Callback function must be set for Jobs %s callback.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check client token length. */
    if( pRequestInfo->pClientToken != AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE )
    {
        if( pRequestInfo->clientTokenLength == 0 )
        {
            IotLogError( "Client token length must be set for Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->clientTokenLength > AWS_IOT_CLIENT_TOKEN_MAX_LENGTH )
        {
            IotLogError( "Client token for Jobs %s cannot be longer than %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         AWS_IOT_CLIENT_TOKEN_MAX_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check Job ID for DESCRIBE and UPDATE. */
    if( ( type == JOBS_DESCRIBE ) || ( type == JOBS_UPDATE ) )
    {
        if( ( pRequestInfo->pJobId == NULL ) || ( pRequestInfo->jobIdLength == 0 ) )
        {
            IotLogError( "Job ID must be set for Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->jobIdLength > JOBS_MAX_ID_LENGTH )
        {
            IotLogError( "Job ID for Jobs %s cannot be longer than %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         JOBS_MAX_ID_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _validateUpdateInfo( _jobsOperationType_t type,
                                              const AwsIotJobsUpdateInfo_t * pUpdateInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );

    /* Only START NEXT and UPDATE operations need an update info. */
    AwsIotJobs_Assert( ( type == JOBS_START_NEXT ) || ( type == JOBS_UPDATE ) );

    /* Check that Job status to report is valid for Jobs UPDATE. */
    if( type == JOBS_UPDATE )
    {
        switch( pUpdateInfo->newStatus )
        {
            case AWS_IOT_JOB_STATE_IN_PROGRESS:
            case AWS_IOT_JOB_STATE_FAILED:
            case AWS_IOT_JOB_STATE_SUCCEEDED:
            case AWS_IOT_JOB_STATE_REJECTED:
                break;

            default:
                IotLogError( "Job state %s is not valid for Jobs UPDATE.",
                             AwsIotJobs_StateName( pUpdateInfo->newStatus ) );

                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check that step timeout is valid. */
    if( pUpdateInfo->stepTimeoutInMinutes != AWS_IOT_JOBS_NO_TIMEOUT )
    {
        if( pUpdateInfo->stepTimeoutInMinutes < 1 )
        {
            IotLogError( "Step timeout for Jobs %s must be at least 1.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
        else if( pUpdateInfo->stepTimeoutInMinutes > JOBS_MAX_TIMEOUT )
        {
            IotLogError( "Step timeout for Jobs %s cannot exceed %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         JOBS_MAX_TIMEOUT );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check status details. */
    if( pUpdateInfo->pStatusDetails != AWS_IOT_JOBS_NO_STATUS_DETAILS )
    {
        if( pUpdateInfo->statusDetailsLength == 0 )
        {
            IotLogError( "Status details length not set for Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pUpdateInfo->statusDetailsLength > JOBS_MAX_STATUS_DETAILS_LENGTH )
        {
            IotLogError( "Status details length for Jobs %s cannot exceed %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         JOBS_MAX_STATUS_DETAILS_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_Init( uint32_t mqttTimeoutMs )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_SUCCESS;

    bool listInitStatus = AwsIot_InitLists( &_AwsIotJobsPendingOperations,
                                            &_AwsIotJobsSubscriptions,
                                            &_AwsIotJobsPendingOperationsMutex,
                                            &_AwsIotJobsSubscriptionsMutex );

    if( listInitStatus == false )
    {
        IotLogInfo( "Failed to create Jobs lists." );

        status = AWS_IOT_JOBS_INIT_FAILED;
    }
    else
    {
        /* Save the MQTT timeout option. */
        if( mqttTimeoutMs != 0 )
        {
            _AwsIotJobsMqttTimeoutMs = mqttTimeoutMs;
        }

        IotLogInfo( "Jobs library successfully initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void AwsIotJobs_Cleanup( void )
{
    /* Remove and free all items in the Jobs pending operation list. */
    IotMutex_Lock( &_AwsIotJobsPendingOperationsMutex );
    IotListDouble_RemoveAll( &_AwsIotJobsPendingOperations,
                             _AwsIotJobs_DestroyOperation,
                             offsetof( _jobsOperation_t, link ) );
    IotMutex_Unlock( &_AwsIotJobsPendingOperationsMutex );

    /* Remove and free all items in the Jobs subscription list. */
    IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
    IotListDouble_RemoveAll( &_AwsIotJobsSubscriptions,
                             _AwsIotJobs_DestroySubscription,
                             offsetof( _jobsSubscription_t, link ) );
    IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

    /* Restore the default MQTT timeout. */
    _AwsIotJobsMqttTimeoutMs = AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS;

    /* Destroy Jobs library mutexes. */
    IotMutex_Destroy( &_AwsIotJobsPendingOperationsMutex );
    IotMutex_Destroy( &_AwsIotJobsSubscriptionsMutex );

    IotLogInfo( "Jobs library cleanup done." );
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_GetPending( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                         uint32_t flags,
                                         const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                         AwsIotJobsOperation_t * const pGetPendingOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;

    /* Check request info. */
    status = _validateRequestInfo( JOBS_GET_PENDING,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pGetPendingOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    status = _AwsIotJobs_CreateOperation( JOBS_GET_PENDING,
                                          pRequestInfo,
                                          NULL,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pGetPendingOperation != NULL )
    {
        *pGetPendingOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pGetPendingOperation != NULL ) )
    {
        *pGetPendingOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_StartNext( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                        const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                        uint32_t flags,
                                        const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                        AwsIotJobsOperation_t * const pStartNextOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;
    _jsonRequestContents_t requestContents = { 0 };

    /* Check request info. */
    status = _validateRequestInfo( JOBS_START_NEXT,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pStartNextOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Check update info. */
    status = _validateUpdateInfo( JOBS_START_NEXT,
                                  pUpdateInfo );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    requestContents.pUpdateInfo = pUpdateInfo;

    status = _AwsIotJobs_CreateOperation( JOBS_START_NEXT,
                                          pRequestInfo,
                                          &requestContents,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pStartNextOperation != NULL )
    {
        *pStartNextOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pStartNextOperation != NULL ) )
    {
        *pStartNextOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_Describe( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                       int32_t executionNumber,
                                       bool includeJobDocument,
                                       uint32_t flags,
                                       const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                       AwsIotJobsOperation_t * const pDescribeOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;
    _jsonRequestContents_t requestContents = { 0 };

    /* Check request info. */
    status = _validateRequestInfo( JOBS_DESCRIBE,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pDescribeOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    requestContents.describe.executionNumber = executionNumber;
    requestContents.describe.includeJobDocument = includeJobDocument;

    status = _AwsIotJobs_CreateOperation( JOBS_DESCRIBE,
                                          pRequestInfo,
                                          &requestContents,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pDescribeOperation != NULL )
    {
        *pDescribeOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pDescribeOperation != NULL ) )
    {
        *pDescribeOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_Update( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                     const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                     uint32_t flags,
                                     const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                     AwsIotJobsOperation_t * const pUpdateOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;
    _jsonRequestContents_t requestContents = { 0 };

    /* Check request info. */
    status = _validateRequestInfo( JOBS_UPDATE,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pUpdateOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Check update info. */
    status = _validateUpdateInfo( JOBS_UPDATE,
                                  pUpdateInfo );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    requestContents.pUpdateInfo = pUpdateInfo;

    status = _AwsIotJobs_CreateOperation( JOBS_UPDATE,
                                          pRequestInfo,
                                          &requestContents,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pUpdateOperation != NULL )
    {
        *pUpdateOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pUpdateOperation != NULL ) )
    {
        *pUpdateOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_Wait( AwsIotJobsOperation_t operation,
                                   uint32_t timeoutMs,
                                   const char ** const pResponse,
                                   size_t * const pResponseLength )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );

    /* Check that reference is set. */
    if( operation == NULL )
    {
        IotLogError( "Operation reference cannot be NULL." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check that reference is waitable. */
    if( ( operation->flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == 0 )
    {
        IotLogError( "Operation is not waitable." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check that output parameters are set. */
    if( ( pResponse == NULL ) || ( pResponseLength == NULL ) )
    {
        IotLogError( "Output buffer and size pointer must be set for Jobs %s.",
                     _pAwsIotJobsOperationNames[ operation->type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Wait for a response to the Jobs operation. */
    if( IotSemaphore_TimedWait( &( operation->notify.waitSemaphore ),
                                timeoutMs ) == true )
    {
        status = operation->status;
    }
    else
    {
        status = AWS_IOT_JOBS_TIMEOUT;
    }

    /* Remove the completed operation from the pending operation list. */
    IotMutex_Lock( &( _AwsIotJobsPendingOperationsMutex ) );
    IotListDouble_Remove( &( operation->link ) );
    IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );

    /* Decrement the reference count. This also removes subscriptions if the
     * count reaches 0. */
    IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
    _AwsIotJobs_DecrementReferences( operation,
                                     operation->pSubscription->pTopicBuffer,
                                     NULL );
    IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

    /* Set the output parameters. Jobs responses are available on success or
     * when the Jobs service returns an error document. */
    if( ( status == AWS_IOT_JOBS_SUCCESS ) || ( status > AWS_IOT_JOBS_INVALID_TOPIC ) )
    {
        AwsIotJobs_Assert( operation->pJobsResponse != NULL );
        AwsIotJobs_Assert( operation->jobsResponseLength > 0 );

        *pResponse = operation->pJobsResponse;
        *pResponseLength = operation->jobsResponseLength;
    }

    /* Destroy the Jobs operation. */
    _AwsIotJobs_DestroyOperation( operation );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

const char * AwsIotJobs_strerror( AwsIotJobsError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case AWS_IOT_JOBS_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case AWS_IOT_JOBS_STATUS_PENDING:
            pMessage = "STATUS PENDING";
            break;

        case AWS_IOT_JOBS_INIT_FAILED:
            pMessage = "INIT FAILED";
            break;

        case AWS_IOT_JOBS_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case AWS_IOT_JOBS_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case AWS_IOT_JOBS_MQTT_ERROR:
            pMessage = "MQTT ERROR";
            break;

        case AWS_IOT_JOBS_BAD_RESPONSE:
            pMessage = "BAD RESPONSE";
            break;

        case AWS_IOT_JOBS_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case AWS_IOT_JOBS_INVALID_TOPIC:
            pMessage = "FAILED: INVALID TOPIC";
            break;

        case AWS_IOT_JOBS_INVALID_JSON:
            pMessage = "FAILED: INVALID JSON";
            break;

        case AWS_IOT_JOBS_INVALID_REQUEST:
            pMessage = "FAILED: INVALID REQUEST";
            break;

        case AWS_IOT_JOBS_INVALID_STATE:
            pMessage = "FAILED: INVALID STATE TRANSITION";
            break;

        case AWS_IOT_JOBS_NOT_FOUND:
            pMessage = "FAILED: NOT FOUND";
            break;

        case AWS_IOT_JOBS_VERSION_MISMATCH:
            pMessage = "FAILED: VERSION MISMATCH";
            break;

        case AWS_IOT_JOBS_INTERNAL_ERROR:
            pMessage = "FAILED: INTERNAL ERROR";
            break;

        case AWS_IOT_JOBS_THROTTLED:
            pMessage = "FAILED: THROTTLED";
            break;

        case AWS_IOT_JOBS_TERMINAL_STATE:
            pMessage = "FAILED: TERMINAL STATE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

const char * AwsIotJobs_StateName( AwsIotJobState_t state )
{
    const char * pMessage = NULL;

    switch( state )
    {
        case AWS_IOT_JOB_STATE_QUEUED:
            pMessage = "QUEUED";
            break;

        case AWS_IOT_JOB_STATE_IN_PROGRESS:
            pMessage = "IN PROGRESS";
            break;

        case AWS_IOT_JOB_STATE_FAILED:
            pMessage = "FAILED";
            break;

        case AWS_IOT_JOB_STATE_SUCCEEDED:
            pMessage = "SUCCEEDED";
            break;

        case AWS_IOT_JOB_STATE_CANCELED:
            pMessage = "CANCELED";
            break;

        case AWS_IOT_JOB_STATE_TIMED_OUT:
            pMessage = "TIMED OUT";
            break;

        case AWS_IOT_JOB_STATE_REJECTED:
            pMessage = "REJECTED";
            break;

        case AWS_IOT_JOB_STATE_REMOVED:
            pMessage = "REMOVED";
            break;

        default:
            pMessage = "INVALID STATE";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/
