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
 * @brief Demonstrates use of the AWS IoT Jobs library.
 */

/* Config include. Should always come first per the style guide. */
#include "iot_config.h"

/* Demo logging. */
#include "iot_demo_logging.h"

/* Platform Includes. */
#include "platform/iot_clock.h"

/* MQTT Include. The underlying protocol for this demo. */
#include "iot_atomic.h"
#include "iot_mqtt.h"

/* JSON Utilies for pulling out values. */
#include "iot_json_utils.h"

/* Jobs Library. */
#include "aws_iot_jobs.h"

/**
 * @brief The Library Timeout.
 */
#define TIMEOUT_MS                      ( 5000u )

/**
 * @brief The MQTT Library keepalive time.
 */
#define KEEP_ALIVE_SECONDS              ( 60 )

/**
 * @brief The key of the Job ID.
 */
#define JOB_ID_KEY                      "jobId"

/**
 * @brief the length of the Job ID Key.
 */
#define JOB_ID_KEY_LENGTH               ( sizeof( JOB_ID_KEY ) - 1 )

/**
 * @brief The Job Document Key.
 */
#define JOB_DOC_KEY                     "jobDocument"

/**
 * @brief the length of the Job Document Key.
 *
 * This key is sent by the Jobs Service.
 */
#define JOB_DOC_KEY_LENGTH              ( sizeof( JOB_DOC_KEY ) - 1 )

/**
 * @brief The Job Action Key for the Job Document.
 *
 * This key is sent from the service user via the Job Document.
 */
#define JOB_ACTION_KEY                  "action"

/**
 * @brief the length of the Action Key.
 */
#define JOB_ACTION_KEY_LENGTH           ( sizeof( JOB_ACTION_KEY ) - 1 )

/**
 * @brief The Message Key for the Job Document.
 *
 * This key is sent from the service user via the Job Document.
 */
#define JOB_MESSAGE_KEY                 "message"

/**
 * @brief the length of the Message Key.
 *
 * This key is sent from the service user via the Job Document.
 */
#define JOB_MESSAGE_KEY_LENGTH          ( sizeof( JOB_MESSAGE_KEY ) - 1 )

/**
 * @brief The Topic Key for the Job Document.
 *
 * This key is sent from the service user via the Job Document. It is used for
 * the MQTT topic for the publish command.
 */
#define JOB_TOPIC_KEY                   "topic"

/**
 * @brief the length of the Topic Key.
 */
#define JOB_TOPIC_KEY_LENGTH            ( sizeof( JOB_TOPIC_KEY ) - 1 )

/**
 * @brief Max Length for the ID.
 */
#define JOBS_DEMO_MAX_ID_LENGTH         64

/**
 * @brief Max Length for Job Document.
 */
#define JOBS_DEMO_MAX_JOB_DOC_LENGTH    128

/**
 * @brief A flag for signaling the end of the demo.
 */
uint32_t finishFlag = 0;

/**
 * @brief Flag value for signaling that the demo is finished.
 */
#define JOBS_DEMO_FINISHED    1

/**
 * @brief Flag value for signaling that the demo is still running.
 */
#define JOBS_DEMO_RUNNING     0

/**
 * @brief Execute the Jobs Demo.
 *
 * This is the top level function called by the IOT Demo harness.
 */
int RunJobsDemo( bool awsIotMqttMode,
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
static int _initDemo( void )
{
    int status = EXIT_SUCCESS;
    IotMqttError_t mqttInitStatus = IOT_MQTT_SUCCESS;
    AwsIotJobsError_t jobsInitStatus = AWS_IOT_JOBS_SUCCESS;

    mqttInitStatus = IotMqtt_Init();

    if( mqttInitStatus != IOT_MQTT_SUCCESS )
    {
        status = EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        jobsInitStatus = AwsIotJobs_Init( 0 );

        if( jobsInitStatus != AWS_IOT_JOBS_SUCCESS )
        {
            IotMqtt_Cleanup();
            status = EXIT_FAILURE;
        }
    }

    return status;
}

/**
 * @brief Execute actions sent through the jobs service.
 *
 * @param[in] command String containing command to execute.
 * @param[in] commandLength Length of the command string.
 * @param[in] mqttConnection MQTT Connection used by _publish_.
 * @param[in] jobDoc JSON String passed by the jobs library.
 * @param[in] jobDocLength Length of the jobDoc string.
 * @param[in] exitFlag Flag used by the _exit_ command to signal the demo completion.
 *
 * Executes various commands:
 * 1. The "publish" command will publish a string to a specified topic.
 *
 *   An example JSON doc:
 * ```
 * {"action":"publish","message":"Hello world!","topic":"jobsdemo/1"}
 * ```
 *
 *  This will publish "Hello world!" to the topic "jobsdemo/1". A user with
 *  access to the AWS IoT console can view this message in the "test" section.
 *
 *  If message or topic are missing from the JSON Job document, the execution
 *  will fail.
 *
 * 2. The "print" command prints the message to console (with quotes if it's a JSON string).
 *
 *   An example JSON doc:
 * ```
 * {"action":"print","message":"Hello world!"}
 * ```
 *
 *   This will print "Hello world!" in the device log.
 *
 *   If message is missing from the JSON job document, the execution will fail.
 *
 * 3. The "exit" command signals main to stop looping.
 *
 *   An example JSON doc:
 * ```
 * {"action":"exit"}
 * ```
 *
 **/
static bool _executeAction( const char * command,
                            size_t commandLength,
                            IotMqttConnection_t const mqttConnection,
                            const char * jobDoc,
                            size_t jobDocLength,
                            bool * exitFlag )
{
    bool status = false;
    const char * pMessage = NULL;
    size_t messageLength = 0;

    if( strncmp( command, "publish", commandLength ) == 0 )
    {
        const char * pTopic = NULL;
        size_t topicLength = 0;

        if( IotJsonUtils_FindJsonValue( jobDoc, jobDocLength, JOB_MESSAGE_KEY, JOB_MESSAGE_KEY_LENGTH, &pMessage, &messageLength ) &&
            IotJsonUtils_FindJsonValue( jobDoc, jobDocLength, JOB_TOPIC_KEY, JOB_TOPIC_KEY_LENGTH, &pTopic, &topicLength ) )
        {
            IotMqttError_t err = IOT_MQTT_SUCCESS;
            IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

            IotLogInfo( "Executing Publish of %.*s", messageLength, pMessage );
            IotLogInfo( "Topic: %.*s", topicLength, pTopic );

            publishInfo.qos = IOT_MQTT_QOS_0;
            publishInfo.topicNameLength = ( uint16_t ) topicLength - 2U;
            publishInfo.pTopicName = pTopic + 1;
            publishInfo.payloadLength = messageLength - 2;
            publishInfo.pPayload = pMessage + 1;
            publishInfo.retryMs = 5000;
            publishInfo.retryLimit = 10;

            err = IotMqtt_PublishAsync( mqttConnection, &publishInfo, 0, NULL, NULL );

            status = err == IOT_MQTT_SUCCESS;
        }
        else
        {
            IotLogInfo( "Failed to execute publish. Could not find the \"topic\" or \"message\" key" );
        }
    }

    else if( strncmp( command, "print", commandLength ) == 0 )
    {
        if( IotJsonUtils_FindJsonValue( jobDoc, jobDocLength, JOB_MESSAGE_KEY, JOB_MESSAGE_KEY_LENGTH, &pMessage, &messageLength ) )
        {
            IotLogInfo( "%.*s", messageLength, pMessage );
            status = true;
        }
        else
        {
            IotLogInfo( "Failed to execute print." );
        }
    }

    /*
     */
    else if( strncmp( command, "exit", commandLength ) == 0 )
    {
        *exitFlag = true;
        status = true;
    }
    else
    {
        IotLogError( "Unrecognized command: %.*s", commandLength, command );
    }

    return status;
}

/**
 *  @brief A callback for the Update Async Call to log any errors.
 */
static void _updateResultCallback( void * param1,
                                   AwsIotJobsCallbackParam_t * cbParam )
{
    AwsIotJobsError_t result = cbParam->u.operation.result;
    bool isExit = ( bool ) param1;

    if( isExit )
    {
        IotLogInfo( "Got Exit Flag" );
        Atomic_CompareAndSwap_u32( &finishFlag, JOBS_DEMO_FINISHED, JOBS_DEMO_RUNNING );
    }

    IotLogInfo( "Job Update complete with result %s", AwsIotJobs_strerror( result ) );
}

/**
 * @brief A callback for the StartNext Async call to report any errors.
 */
static void _startNextCallback( void * param1,
                                AwsIotJobsCallbackParam_t * cbParam )
{
    AwsIotJobsError_t result = cbParam->u.operation.result;

    IotLogError( "Start Next complete with result %s", AwsIotJobs_strerror( result ) );
}

/**
 * @brief Get and update the job.
 */
static bool _executeDemo( IotMqttConnection_t const mqttConnection,
                          const char * pThingName,
                          size_t thingNameLength,
                          const char * pJobId,
                          size_t jobIdLength,
                          const char * jobDoc,
                          size_t jobDocLength )
{
    bool success = false;
    AwsIotJobsError_t err = AWS_IOT_JOBS_SUCCESS;
    AwsIotJobState_t result = AWS_IOT_JOB_STATE_FAILED;
    AwsIotJobsRequestInfo_t req = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsCallbackInfo_t startNextCBInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    AwsIotJobsCallbackInfo_t updateResultCBInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    const char * pAction = NULL;
    size_t actionLength = 0;
    bool exitFlag = false;

    req.mqttConnection = mqttConnection;
    req.pThingName = pThingName;
    req.thingNameLength = thingNameLength;
    req.pJobId = pJobId + 1;
    req.jobIdLength = jobIdLength - 2;
    req.mallocResponse = malloc;

    IotLogError( "Job Doc in Execute Demo: %.*s", jobDocLength, jobDoc );

    /* Check that a job notification came in. */
    if( pJobId[ 0 ] != '\0' )
    {
        /* Update Job to IN_PROGRESS. */
        startNextCBInfo.function = _startNextCallback;

        err = AwsIotJobs_StartNextAsync( &req, &updateInfo, 0, &startNextCBInfo, NULL );

        if( err != AWS_IOT_JOBS_STATUS_PENDING )
        {
            IotLogError( "Start Next Failed: %s", AwsIotJobs_strerror( err ) );
            success = false;
        }
        else
        {
            success = true;
        }

        /* Parse out the action. */
        if( success )
        {
            success = IotJsonUtils_FindJsonValue( jobDoc, jobDocLength, JOB_ACTION_KEY, JOB_ACTION_KEY_LENGTH, &pAction, &actionLength );

            if( !success )
            {
                IotLogError( "Failed to find %s Key.", JOB_ACTION_KEY );
            }
        }

        /* Execute on the action without quotes. */
        if( _executeAction( pAction + 1, actionLength - 2, mqttConnection, jobDoc, jobDocLength, &exitFlag ) )
        {
            result = AWS_IOT_JOB_STATE_SUCCEEDED;
        }
        else
        {
            result = AWS_IOT_JOB_STATE_FAILED;
        }

        updateInfo.newStatus = result;
        updateResultCBInfo.function = _updateResultCallback;
        updateResultCBInfo.pCallbackContext = ( void * ) exitFlag;

        err = AwsIotJobs_UpdateAsync( &req, &updateInfo, 0, &updateResultCBInfo, NULL );

        if( err != AWS_IOT_JOBS_STATUS_PENDING )
        {
            IotLogError( "Update Result Failed: %s", AwsIotJobs_strerror( err ) );
            success = false;
        }
        else
        {
            success = true;
        }
    }

    return success;
}

/**
 * @brief The Notify Next Callback
 */
static void _jobsCallback( void * param1,
                           AwsIotJobsCallbackParam_t * pCallbackInfo )
{
    bool idKeyFound = false;
    bool docKeyFound = false;

    const char * jobId = NULL;
    size_t jobIdLength = 0;

    const char * jobDoc = NULL;
    size_t jobDocLength = 0;

    /* Get the Job ID */
    idKeyFound = IotJsonUtils_FindJsonValue( pCallbackInfo->u.callback.pDocument, pCallbackInfo->u.callback.documentLength, JOB_ID_KEY, JOB_ID_KEY_LENGTH, &jobId, &jobIdLength );

    IotLogInfo( "Got Notify Next Call." );

    if( idKeyFound )
    {
        IotLogInfo( "New Job: %.*s", jobIdLength, jobId );

        if( jobIdLength > JOBS_DEMO_MAX_ID_LENGTH )
        {
            idKeyFound = false;
            IotLogError( "Job ID is too long." );
        }
    }
    else
    {
        IotLogError( "Failed to parse JobID from Notify Next." );
        IotLogError( "document: %.*s", pCallbackInfo->u.callback.documentLength, pCallbackInfo->u.callback.pDocument );
    }

    /* Get the Job Document */
    if( idKeyFound )
    {
        docKeyFound = IotJsonUtils_FindJsonValue( pCallbackInfo->u.callback.pDocument, pCallbackInfo->u.callback.documentLength, JOB_DOC_KEY, JOB_DOC_KEY_LENGTH, &jobDoc, &jobDocLength );
    }

    if( docKeyFound )
    {
        if( jobDocLength > JOBS_DEMO_MAX_JOB_DOC_LENGTH )
        {
            docKeyFound = false;
            IotLogError( "Job document is too long." );
        }

        /* Execute the demo */
        _executeDemo( pCallbackInfo->mqttConnection,
                      pCallbackInfo->pThingName,
                      pCallbackInfo->thingNameLength,
                      jobId,
                      jobIdLength,
                      jobDoc,
                      jobDocLength );
    }

    if( !idKeyFound )
    {
        IotLogError( "Failed to parse Job ID in Notify Next callback." );
    }

    if( !docKeyFound )
    {
        IotLogError( "Failed to parse Job Document in Notify Next callback." );
    }
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
static int _establishMqttConnection( const char * pIdentifier,
                                     void * pNetworkServerInfo,
                                     void * pNetworkCredentialInfo,
                                     const IotNetworkInterface_t * pNetworkInterface,
                                     IotMqttConnection_t * const pMqttConnection )
{
    int status = EXIT_SUCCESS;
    IotMqttError_t connectStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttNetworkInfo_t networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

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
    connectStatus = IotMqtt_Connect( &networkInfo, &connectInfo, TIMEOUT_MS, pMqttConnection );

    if( connectStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "MQTT CONNECT returned error %s.", IotMqtt_strerror( connectStatus ) );

        status = EXIT_FAILURE;
    }

    return status;
}

int RunJobsDemo( bool awsIotMqttMode,
                 const char * pIdentifier,
                 void * pNetworkServerInfo,
                 void * pNetworkCredentialInfo,
                 const IotNetworkInterface_t * pNetworkInterface )
{
    int status = EXIT_SUCCESS;
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    AwsIotJobsError_t err = AWS_IOT_JOBS_SUCCESS;
    size_t thingNameLength = 0;

    bool initialized = false;
    bool connected = false;

    callbackInfo.function = _jobsCallback;
    callbackInfo.pCallbackContext;

    if( status == EXIT_SUCCESS )
    {
        thingNameLength = strlen( pIdentifier );

        if( thingNameLength == 0 )
        {
            IotLogError( "The length of the Thing Name (identifier) must be nonzero." );
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
        status = _establishMqttConnection(
            pIdentifier, pNetworkServerInfo, pNetworkCredentialInfo, pNetworkInterface, &mqttConnection );
        connected = status == EXIT_SUCCESS;
    }

    if( status == EXIT_SUCCESS )
    {
        err = AwsIotJobs_SetNotifyNextCallback( mqttConnection, pIdentifier, thingNameLength, 0, &callbackInfo );

        status = err == AWS_IOT_JOBS_SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    if( status == EXIT_SUCCESS )
    {
        IotLogInfo( "--- Add Job using AWS CLI --- \r\n" ); /* Add an extra line for emphasis. */

        for( ; ; )
        {
            if( Atomic_CompareAndSwap_u32( &finishFlag, 0, JOBS_DEMO_FINISHED ) == 1 )
            {
                break;
            }

            IotClock_SleepMs( 1000 );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        callbackInfo.oldFunction = _jobsCallback;
        callbackInfo.function = NULL;
        err = AwsIotJobs_SetNotifyNextCallback( mqttConnection, pIdentifier, thingNameLength, 0, &callbackInfo );

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
