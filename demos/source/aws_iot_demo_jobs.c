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
 * @file aws_iot_demo_jobs.c
 * @brief Demonstrates use of the AWS Jobs library.
 *
 *
 * # Setup
 */

/* Config include. Should always come first per the style guide. */
#include "iot_config.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/* Demo logging. */
#include "iot_demo_logging.h"

/* Platform Includes. */
#include "platform/iot_clock.h"
#include "platform/iot_network.h"
#include "platform/iot_threads.h"

/* MQTT Include. The underlying protocol for this demo. */
#include "iot_mqtt.h"

/* JSON Utilies for pulling out values. */
#include "iot_json_utils.h"

/* Jobs Library. */
#include "aws_iot_jobs.h"
#include "types/aws_iot_jobs_types.h"

/**
 * @brief The Jobs Library MQTT timeout.
 * @TODO: Figure out how this interacts with the MQTT library timeout.
 */
#define AWS_IOT_DEMO_JOBS_MQTT_TIMEOUT ( 1000U )

/**
 * @brief The MQTT Library timeout.
 */
#define TIMEOUT_MS ( 5000u )

/**
 * @brief The MQTT Library keepalive time.
 */
#define KEEP_ALIVE_SECONDS ( 60 )

/**
 * @brief The key of the Job ID.
 */
#define JOB_ID_KEY        "jobId"
#define JOB_ID_KEY_LENGTH ( sizeof( JOB_ID_KEY ) - 1 )

/**
 * @brief The key of the Job Document.
 */
#define JOB_DOC_KEY        "jobDocument"
#define JOB_DOC_KEY_LENGTH ( sizeof( JOB_DOC_KEY ) - 1 )

#define JOB_ACTION_KEY        "action"
#define JOB_ACTION_KEY_LENGTH ( sizeof( JOB_ACTION_KEY ) - 1 )

#define JOB_MESSAGE_KEY        "message"
#define JOB_MESSAGE_KEY_LENGTH ( sizeof( JOB_MESSAGE_KEY ) - 1 )

#define JOBS_DEMO_MAX_ID_LENGTH      64
#define JOBS_DEMO_MAX_JOB_DOC_LENGTH 64
/**
 * @brief The previous JobId and length
 */
static char _pJobId[ JOBS_DEMO_MAX_ID_LENGTH + 1 ] = {0};
static size_t _JobIdLength = 0;

/**
 * @brief The Job Document which will be passed into the Notify Next callback.
 */
static char _jobDoc[ JOBS_DEMO_MAX_JOB_DOC_LENGTH + 1 ] = {0};
static size_t _jobDocLength = 0;

/**
 * @brief Execute the Jobs Demo.
 *
 * This is the top level function called by the IOT Demo harness.
 */
int32_t RunJobsDemo( bool awsIotMqttMode,
                     const char * pIdentifier,
                     void * pNetworKServerInfo,
                     void * pNetworkCredentialInfo,
                     const IotNetworkInterface_t * pNetworkInterface );

/**
 * @brief Initialize The Jobs Demo.
 *
 * Initialize MQTT module then the Jobs module. If the Jobs module fails
 * to initialize, MQTT cleanup is invoked.
 *
 * @return EXIT_SUCCESS if initialization succeeds. Otherwise EXIT_FAILURE.
 */
static int32_t _initDemo( void )
{
    int32_t status = EXIT_SUCCESS;
    IotMqttError_t mqttInitStatus = IOT_MQTT_SUCCESS;
    AwsIotJobsError_t jobsInitStatus = AWS_IOT_JOBS_SUCCESS;

    mqttInitStatus = IotMqtt_Init();

    if( mqttInitStatus != IOT_MQTT_SUCCESS )
    {
        status = EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        jobsInitStatus = AwsIotJobs_Init( AWS_IOT_DEMO_JOBS_MQTT_TIMEOUT );

        if( jobsInitStatus != AWS_IOT_JOBS_SUCCESS )
        {
            IotMqtt_Cleanup();
            status = EXIT_FAILURE;
        }
    }

    return status;
}

/**
 * @brief The callback when a new job is posted. It signals main via a semaphore.
 */
static void _jobsCallback( void * param1,
                           AwsIotJobsCallbackParam_t * pCallbackInfo )
{
    bool success = false;
    const char * pJsonValue = NULL;
    size_t jsonValueLength = 0;
    IotSemaphore_t * pWaitSem = ( IotSemaphore_t * ) param1;

    IotLogInfo( "Job Doc Len : %d", pCallbackInfo->u.callback.documentLength );
    IotLogInfo( "Job Document: %s", pCallbackInfo->u.callback.pDocument );

    /* Get the Job ID */
    success =
        IotJsonUtils_FindJsonValue( pCallbackInfo->u.callback.pDocument,
                                    pCallbackInfo->u.callback.documentLength,
                                    JOB_ID_KEY,
                                    JOB_ID_KEY_LENGTH,
                                    &pJsonValue,
                                    &jsonValueLength );
    if( success )
    {
        IotLogInfo( "New Job: %.*s", jsonValueLength, pJsonValue );
        memcpy( _pJobId, pJsonValue, jsonValueLength );
        _JobIdLength = jsonValueLength;
    }
    else
    {
        IotLogError( "Failed to parse JobID from Notify Next." );
    }

    /* Get the Job Document */
    success =
        IotJsonUtils_FindJsonValue( pCallbackInfo->u.callback.pDocument,
                                    pCallbackInfo->u.callback.documentLength,
                                    JOB_DOC_KEY,
                                    JOB_DOC_KEY_LENGTH,
                                    &pJsonValue,
                                    &jsonValueLength );

    if( success )
    {
        IotLogInfo( "New Job Doc: %.*s", jsonValueLength, pJsonValue );
        memcpy( _jobDoc, pJsonValue, jsonValueLength );
        _jobDocLength = jsonValueLength;
    }
    else
    {
        IotLogError( "Failed to parse Job Document from Notify Next." );
    }

    /* Signal Main to continue with the demo. */
    IotSemaphore_Post( pWaitSem );
}

/**
 * @brief A helper to extract "message" from the job document.
 * @param[out] msg The location of the message buffer.
 * @param[out] msgLength the length of the message buffer.
 * @returns a bool. true if successful
 */
bool _getMessage( const char ** msg, size_t * msgLength )
{
    return IotJsonUtils_FindJsonValue( _jobDoc,
                                       _jobDocLength,
                                       JOB_MESSAGE_KEY,
                                       JOB_MESSAGE_KEY_LENGTH,
                                       msg,
                                       msgLength );
}

/**
 *@brief A helper to extract "action" from the job document.
 */
bool _getAction( const char ** action, size_t * actionLength )
{
    return IotJsonUtils_FindJsonValue( _jobDoc,
                                       _jobDocLength,
                                       JOB_ACTION_KEY,
                                       JOB_ACTION_KEY_LENGTH,
                                       action,
                                       actionLength );
}

/**
 * @brief Get and update the job.
 */
static int32_t _executeDemo( IotMqttConnection_t const mqttConnection,
                             const char * pThingName,
                             size_t thingNameLength )
{
    bool success = true;
    AwsIotJobsError_t err = AWS_IOT_JOBS_SUCCESS;
    AwsIotJobState_t result = AWS_IOT_JOB_STATE_FAILED;
    AwsIotJobsResponse_t resp = AWS_IOT_JOBS_RESPONSE_INITIALIZER;
    AwsIotJobsRequestInfo_t req = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    const char * pAction = NULL;
    size_t actionLength = 0;
    const char * pMessage = NULL;
    size_t messageLength = 0;

    req.mqttConnection = mqttConnection;
    req.pThingName = pThingName;
    req.thingNameLength = thingNameLength;
    req.pJobId = _pJobId + 1;
    req.jobIdLength = _JobIdLength - 2;
    req.mallocResponse = malloc;

    /* Check that a job notification came in. */
    if( _pJobId[ 0 ] != '\0' )
    {
        /* Update Job to IN_PENDING. */
        updateInfo.newStatus = AWS_IOT_JOB_STATE_IN_PROGRESS;

        err = AwsIotJobs_UpdateSync(
            &req, &updateInfo, 0, AWS_IOT_DEMO_JOBS_MQTT_TIMEOUT, &resp );

        if( err != AWS_IOT_JOBS_SUCCESS )
        {
            IotLogError( "Update Failed: %s", AwsIotJobs_strerror( err ) );
            success = false;
        }
    }

    /* Parse out the action. */
    if( success )
    {
        success = _getAction( &pAction, &actionLength );
        if( !success )
        {
            IotLogError( "Failed to find %s Key.", JOB_ACTION_KEY );
        }
    }

    /* Process the action. */
    if( success )
    {
        /* We are only going to look at the first char after the '"'.
	   This is just to simplify the demo. */
        switch( pAction[ 1 ] )
        {
        case 'p':
            if( _getMessage( &pMessage, &messageLength ) )
            {
                IotLogInfo( "Executing Print: %.*s", messageLength, pMessage );
                result = AWS_IOT_JOB_STATE_SUCCEEDED;
            }
            else
            {
                IotLogInfo( "Failed to execute print." );
                result = AWS_IOT_JOB_STATE_FAILED;
            }
            break;
	case 'w':
		result = AWS_IOT_JOB_STATE_SUCCEEDED;
		IotClock_SleepMs( 10000 );
            /*
	    if ( _getMessage( &pMessage, &messageLength ) )
	    {
		IotLogInfo( "" );
		result = AWS_IOT_JOB_STATE_SUCCEEDED;
	    }
            else
            {
                IotLogInfo( "Failed to execute wait." );
                result = AWS_IOT_JOB_STATE_FAILED;
            }
	    */
	    break;
        default:
            IotLogInfo( "Got unknown command %.*s", actionLength, pAction );
            result = AWS_IOT_JOB_STATE_FAILED;
        }
    }

    /* Update with status. */
    if( success )
    {
        updateInfo.newStatus = result;

        err = AwsIotJobs_UpdateSync(
            &req, &updateInfo, 0, AWS_IOT_DEMO_JOBS_MQTT_TIMEOUT, &resp );

        if( err != AWS_IOT_JOBS_SUCCESS )
        {
            IotLogError( "Update Failed: %s", AwsIotJobs_strerror( err ) );
            success = false;
        }
    }

    return success;
}

/**
 * @brief Clean up the Jobs demo.
 *
 * @note Must not be called if `_initDemo` is not called or does not succeed.
 */
static void _cleanupDemo( void )
{
    AwsIotJobs_Cleanup();
    IotMqtt_Cleanup();
}

/**
 * @brief Establish a new connection to the MQTT server for the Jobs demo.
 *
 * Copied from the shadow demo.
 *
 * @TODO: See if this should be moved up a level and shared or if it's important
 * that it be in one file for the demo.
 *
 * @param[in] pIdentifier NULL-terminated MQTT client identifier. The Jobs
 * demo will use the Thing Name as the client identifier.
 * @param[in] pNetworkServerInfo Passed to the MQTT connect function when
 * establishing the MQTT connection.
 * @param[in] pNetworkCredentialInfo Passed to the MQTT connect function when
 * establishing the MQTT connection.
 * @param[in] pNetworkInterface The network interface to use for this demo.
 * @param[out] pMqttConnection Set to the handle to the new MQTT connection.
 *
 * @return `EXIT_SUCCESS` if the connection is successfully established; `EXIT_FAILURE`
 * otherwise.
 */
static int32_t
_establishMqttConnection( const char * pIdentifier,
                          void * pNetworkServerInfo,
                          void * pNetworkCredentialInfo,
                          const IotNetworkInterface_t * pNetworkInterface,
                          IotMqttConnection_t * const pMqttConnection )
{
    int32_t status = EXIT_SUCCESS;
    IotMqttError_t connectStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttNetworkInfo_t networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    if( ( pIdentifier == NULL ) || ( pIdentifier[ 0 ] == '\0' ) )
    {
        IotLogError( "Thing Name must be provided." );

        status = EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        /* Set the members of the network info not set by the initializer. This
         * struct provided information on the transport layer to the MQTT connection. */
        networkInfo.createNetworkConnection = true;
        networkInfo.u.setup.pNetworkServerInfo = pNetworkServerInfo;
        networkInfo.u.setup.pNetworkCredentialInfo = pNetworkCredentialInfo;
        networkInfo.pNetworkInterface = pNetworkInterface;

        /* Set the members of the connection info not set by the initializer. */
        connectInfo.awsIotMqttMode = true;
        connectInfo.cleanSession = true;
        connectInfo.keepAliveSeconds = KEEP_ALIVE_SECONDS;

        /* AWS IoT recommends the use of the Thing Name as the MQTT client ID. */
        connectInfo.pClientIdentifier = pIdentifier;
        connectInfo.clientIdentifierLength = ( uint16_t ) strlen( pIdentifier );

        IotLogInfo( "Thing Name is %.*s (length %hu).",
                    connectInfo.clientIdentifierLength,
                    connectInfo.pClientIdentifier,
                    connectInfo.clientIdentifierLength );

        /* Establish the MQTT connection. */
        connectStatus = IotMqtt_Connect(
            &networkInfo, &connectInfo, TIMEOUT_MS, pMqttConnection );

        if( connectStatus != IOT_MQTT_SUCCESS )
        {
            IotLogError( "MQTT CONNECT returned error %s.",
                         IotMqtt_strerror( connectStatus ) );

            status = EXIT_FAILURE;
        }
    }

    return status;
}

int32_t RunJobsDemo( bool awsIotMqttMode,
                     const char * pIdentifier,
                     void * pNetworkServerInfo,
                     void * pNetworkCredentialInfo,
                     const IotNetworkInterface_t * pNetworkInterface )
{
    int32_t status = EXIT_SUCCESS;
    bool semaphoreCreate = false;
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    AwsIotJobsCallbackInfo_t callbackInfo =
        AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    AwsIotJobsError_t err = AWS_IOT_JOBS_SUCCESS;
    size_t thingNameLength = 0;
    IotSemaphore_t waitSem;

    bool initialized = false;
    bool connected = false;

    semaphoreCreate = IotSemaphore_Create( &waitSem, 0, 2 );

    callbackInfo.function = _jobsCallback;
    callbackInfo.pCallbackContext = &waitSem;

    if( !semaphoreCreate )
    {
        status = EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        thingNameLength = strlen( pIdentifier );

        if( thingNameLength == 0 )
        {
            IotLogError(
                "The length of the Thing Name (identifier) must be nonzero." );
            status = EXIT_FAILURE;
        }
    }

    if( status == EXIT_SUCCESS )
    {
        status = _initDemo();
        initialized = status == EXIT_SUCCESS;
    }

    if( status == EXIT_SUCCESS )
    {
        status = _establishMqttConnection( pIdentifier,
                                           pNetworkServerInfo,
                                           pNetworkCredentialInfo,
                                           pNetworkInterface,
                                           &mqttConnection );
        connected = status == EXIT_SUCCESS;
    }

    if( status == EXIT_SUCCESS )
    {
        err = AwsIotJobs_SetNotifyNextCallback(
            mqttConnection, pIdentifier, thingNameLength, 0, &callbackInfo );

        status = err == AWS_IOT_JOBS_SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        IotLogInfo( "--- Add Job using AWS CLI --- \r\n" ); /* Add an extra line for emphasis. */
        IotSemaphore_Wait( &waitSem );
        status = _executeDemo( mqttConnection, pIdentifier, thingNameLength );
    }

    if( status == EXIT_SUCCESS )
    {
        err = AwsIotJobs_SetNotifyNextCallback(
            mqttConnection, pIdentifier, thingNameLength, 0, NULL );

        status = err == AWS_IOT_JOBS_SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    if( connected )
    {
        IotMqtt_Disconnect( mqttConnection, 0 );
    }

    if( initialized )
    {
        _cleanupDemo();
    }

    return status;
}
