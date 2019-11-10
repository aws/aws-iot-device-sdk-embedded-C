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
 *
 * This program sets a Jobs Notify-Next callback and waits for Job documents to arrive.
 * It will then take action based on the Job document.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Set up logging for this demo. */
#include "iot_demo_logging.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Jobs include. */
#include "aws_iot_jobs.h"

/* JSON utilities include. */
#include "aws_iot_doc_parser.h"

/* Atomics include. */
#include "iot_atomic.h"

/*-----------------------------------------------------------*/

/**
 * @brief The timeout for Jobs and MQTT operations in this demo.
 */
#define TIMEOUT_MS                ( ( uint32_t ) 5000u )

/**
 * @brief The keep-alive interval used for this demo.
 *
 * An MQTT ping request will be sent periodically at this interval.
 */
#define KEEP_ALIVE_SECONDS        ( ( uint16_t ) 60u )

/**
 * @brief The JSON key of the Job ID.
 *
 * Job documents are JSON documents received from the AWS IoT Jobs service.
 * All Job documents will contain this key, whose value represents the unique
 * identifier of a Job.
 */
#define JOB_ID_KEY                "jobId"

/**
 * @brief The length of #JOB_ID_KEY.
 */
#define JOB_ID_KEY_LENGTH         ( sizeof( JOB_ID_KEY ) - 1 )

/**
 * @brief The JSON key of the Job document.
 *
 * Job documents are JSON documents received from the AWS IoT Jobs service.
 * All Job documents will contain this key, whose value is an application-specific
 * JSON document.
 */
#define JOB_DOC_KEY               "jobDocument"

/**
 * @brief The length of #JOB_DOC_KEY.
 */
#define JOB_DOC_KEY_LENGTH        ( sizeof( JOB_DOC_KEY ) - 1 )

/**
 * @brief The JSON key whose value represents the action this demo should take.
 *
 * This demo program expects this key to be in the Job document. It is a key
 * specific to this demo.
 */
#define JOB_ACTION_KEY            "action"

/**
 * @brief The length of #JOB_ACTION_KEY.
 */
#define JOB_ACTION_KEY_LENGTH     ( sizeof( JOB_ACTION_KEY ) - 1 )

/**
 * @brief A message associated with the Job action.
 *
 * This demo program expects this key to be in the Job document if the "action"
 * is either "publish" or "print". It represents the message that should be
 * published or printed, respectively.
 */
#define JOB_MESSAGE_KEY           "message"

/**
 * @brief The length of #JOB_MESSAGE_KEY.
 */
#define JOB_MESSAGE_KEY_LENGTH    ( sizeof( JOB_MESSAGE_KEY ) - 1 )

/**
 * @brief An MQTT topic associated with the Job "publish" action.
 *
 * This demo program expects this key to be in the Job document if the "action"
 * is "publish". It represents the MQTT topic on which the message should be
 * published.
 */
#define JOB_TOPIC_KEY             "topic"

/**
 * @brief The length of #JOB_TOPIC_KEY.
 */
#define JOB_TOPIC_KEY_LENGTH      ( sizeof( JOB_TOPIC_KEY ) - 1 )

/**
 * @brief The minimum length of a string in a JSON Job document.
 *
 * At the very least the Job ID must have the quotes that identify it as a JSON
 * string and 1 character for the string itself (the string must not be empty).
 */
#define JSON_STRING_MIN_LENGTH    ( ( size_t ) 3 )

/**
 * @brief The maximum length of a Job ID.
 *
 * This limit is defined by AWS service limits. See the following page for more
 * information.
 *
 * https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html#job-limits
 */
#define JOB_ID_MAX_LENGTH         ( ( size_t ) 64 )

/**
 * @brief A value passed as context to #_operationCompleteCallback to specify that
 * it should set the #JOBS_DEMO_FINISHED flag.
 */
#define JOBS_DEMO_SHOULD_EXIT     ( ( void * ) ( ( intptr_t ) 1 ) )

/**
 * @brief Flag value for signaling that the demo is still running.
 *
 * The initial value of #_exitFlag.
 */
#define JOBS_DEMO_RUNNING         ( ( uint32_t ) 0 )

/**
 * @brief Flag value for signaling that the demo is finished.
 *
 * #_exitFlag will be set to this when a Job document with { "action": "exit" }
 * is received.
 */
#define JOBS_DEMO_FINISHED        ( ( uint32_t ) 1 )

/*-----------------------------------------------------------*/

/**
 * @brief Currently supported actions that a Job document can specify.
 */
typedef enum _jobAction
{
    JOB_ACTION_PRINT,   /**< Print a message. */
    JOB_ACTION_PUBLISH, /**< Publish a message to an MQTT topic. */
    JOB_ACTION_EXIT,    /**< Exit the demo. */
    JOB_ACTION_UNKNOWN  /**< Unknown action. */
} _jobAction_t;

/*-----------------------------------------------------------*/

/**
 * @brief Used to print log messages that do not contain any metadata.
 */
static IotLogConfig_t _logHideAll = { .hideLogLevel = true, .hideLibraryName = true, .hideTimestring = true };

/**
 * @brief A flag that signals the end of the demo.
 *
 * When a Job document is received with { "action": "exit" }, the demo will set
 * this flag and exit.
 */
static uint32_t _exitFlag = 0;

/*-----------------------------------------------------------*/

/**
 * @brief Initialize the libraries required for this demo.
 *
 * Initialize the MQTT and Jobs libraries. If the Jobs library fails
 * to initialize, the MQTT library is cleaned up.
 *
 * @return `EXIT_SUCCESS` if all initialization succeeds; `EXIT_FAILURE` otherwise.
 */
static int _initializeDemo( void )
{
    int status = EXIT_SUCCESS;
    IotMqttError_t mqttInitStatus = IOT_MQTT_SUCCESS;
    AwsIotJobsError_t jobsInitStatus = AWS_IOT_JOBS_SUCCESS;

    mqttInitStatus = IotMqtt_Init();

    if( mqttInitStatus != IOT_MQTT_SUCCESS )
    {
        status = EXIT_FAILURE;
    }
    else
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

/*-----------------------------------------------------------*/

/**
 * @brief Clean up the libraries initialized by #_initializeDemo.
 *
 * @note Must not be called if #_initializeDemo was not successfully called.
 */
static void _cleanupDemo( void )
{
    AwsIotJobs_Cleanup();
    IotMqtt_Cleanup();
}

/*-----------------------------------------------------------*/

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

/*-----------------------------------------------------------*/

/**
 * @brief Converts a string in a Job document to a #_jobAction_t.
 *
 * @param[in] pAction The Job action as a string.
 * @param[in] actionLength The length of `pAction`.
 *
 * @return A #_jobAction_t equivalent to the given string.
 */
static _jobAction_t _getAction( const char * pAction,
                                size_t actionLength )
{
    _jobAction_t action = JOB_ACTION_UNKNOWN;

    if( strncmp( pAction, "print", actionLength ) == 0 )
    {
        action = JOB_ACTION_PRINT;
    }
    else if( strncmp( pAction, "publish", actionLength ) == 0 )
    {
        action = JOB_ACTION_PUBLISH;
    }
    else if( strncmp( pAction, "exit", actionLength ) == 0 )
    {
        action = JOB_ACTION_EXIT;
    }

    return action;
}

/*-----------------------------------------------------------*/

/**
 * @brief Extracts a JSON string from the Job document.
 *
 * @param[in] pJsonDoc The JSON document to search.
 * @param[in] jsonDocLength Length of `pJsonDoc`.
 * @param[in] pKey The JSON key to search for.
 * @param[in] keyLength Length of `pKey`.
 * @param[out] pValue The extracted JSON value.
 * @param[out] valueLength Length of pValue.
 *
 * @return `true` if the key was found and the value is valid; `false` otherwise.
 */
static bool _getJsonString( const char * pJsonDoc,
                            size_t jsonDocLength,
                            const char * pKey,
                            size_t keyLength,
                            const char ** pValue,
                            size_t * valueLength )
{
    /*
     * Note: This parser used is specific for parsing AWS IoT document received
     * through a mutually aithenticated connection. This parser will not check
     * for the correctness of the document as it is designed for low memory
     * footprint rather than checking for correctness of the document. This
     * parser is not meant to be used as a general purpose JSON parser.
     */
    bool keyFound = AwsIotDocParser_FindValue( pJsonDoc,
                                               jsonDocLength,
                                               pKey,
                                               keyLength,
                                               pValue,
                                               valueLength );

    if( keyFound == true )
    {
        /* Exclude empty strings. */
        if( *valueLength < JSON_STRING_MIN_LENGTH )
        {
            keyFound = false;
        }
        else
        {
            /* Adjust the value to remove the quotes. */
            ( *pValue )++;
            ( *valueLength ) -= 2;
        }
    }

    return keyFound;
}

/*-----------------------------------------------------------*/

/**
 * @brief Job operation completion callback. This function is invoked when an
 * asynchronous Job operation finishes.
 *
 * @param[in] pCallbackContext Set to a non-NULL value to exit the demo.
 * @param[in] pCallbackParam Information on the Job operation that completed.
 */
static void _operationCompleteCallback( void * pCallbackContext,
                                        AwsIotJobsCallbackParam_t * pCallbackParam )
{
    /* This function is invoked when either a StartNext or Update completes. */
    if( pCallbackParam->callbackType == AWS_IOT_JOBS_START_NEXT_COMPLETE )
    {
        IotLogInfo( "Job StartNext complete with result %s.",
                    AwsIotJobs_strerror( pCallbackParam->u.operation.result ) );
    }
    else
    {
        IotLogInfo( "Job Update complete with result %s.",
                    AwsIotJobs_strerror( pCallbackParam->u.operation.result ) );
    }

    /* If a non-NULL context is given, set the flag to exit the demo. */
    if( pCallbackContext != NULL )
    {
        ( void ) Atomic_CompareAndSwap_u32( &_exitFlag, JOBS_DEMO_FINISHED, JOBS_DEMO_RUNNING );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Process an action with a message, such as "print" or "publish".
 *
 * @param[in] mqttConnection The MQTT connection to use if the action is "publish".
 * @param[in] action Either #JOB_ACTION_PRINT or #JOB_ACTION_PUBLISH.
 * @param[in] pJobDoc A pointer to the Job document.
 * @param[in] jobDocLength The length of the Job document.
 *
 * @return #AWS_IOT_JOB_STATE_SUCCEEDED on success; #AWS_IOT_JOB_STATE_FAILED otherwise.
 */
static AwsIotJobState_t _processMessage( IotMqttConnection_t mqttConnection,
                                         _jobAction_t action,
                                         const char * pJobDoc,
                                         size_t jobDocLength )
{
    AwsIotJobState_t status = AWS_IOT_JOB_STATE_SUCCEEDED;
    IotMqttError_t mqttStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    const char * pMessage = NULL, * pTopic = NULL;
    size_t messageLength = 0, topicLength = 0;

    /* Both "print" and "publish" require a "message" key. Search the Job
     * document for this key. */
    if( _getJsonString( pJobDoc,
                        jobDocLength,
                        JOB_MESSAGE_KEY,
                        JOB_MESSAGE_KEY_LENGTH,
                        &pMessage,
                        &messageLength ) == false )
    {
        IotLogError( "Job document for \"print\" or \"publish\" does not contain a %s key.",
                     JOB_MESSAGE_KEY );

        status = AWS_IOT_JOB_STATE_FAILED;
    }

    if( status == AWS_IOT_JOB_STATE_SUCCEEDED )
    {
        if( action == JOB_ACTION_PRINT )
        {
            /* Print the given message if the action is "print". */
            IotLog( IOT_LOG_INFO, &_logHideAll,
                    "\r\n"
                    "/*-----------------------------------------------------------*/\r\n"
                    "\r\n"
                    "%.*s\r\n"
                    "\r\n"
                    "/*-----------------------------------------------------------*/\r\n"
                    "\r\n", messageLength, pMessage );
        }
        else
        {
            /* Extract the topic if the action is "publish". */
            if( _getJsonString( pJobDoc,
                                jobDocLength,
                                JOB_TOPIC_KEY,
                                JOB_TOPIC_KEY_LENGTH,
                                &pTopic,
                                &topicLength ) == false )
            {
                IotLogError( "Job document for action \"publish\" does not contain a %s key.",
                             JOB_TOPIC_KEY );

                status = AWS_IOT_JOB_STATE_FAILED;
            }

            if( status == AWS_IOT_JOB_STATE_SUCCEEDED )
            {
                publishInfo.qos = IOT_MQTT_QOS_0;
                publishInfo.pTopicName = pTopic;
                publishInfo.topicNameLength = ( uint16_t ) topicLength;
                publishInfo.pPayload = pMessage;
                publishInfo.payloadLength = messageLength;

                mqttStatus = IotMqtt_PublishAsync( mqttConnection, &publishInfo, 0, NULL, NULL );

                if( mqttStatus != IOT_MQTT_SUCCESS )
                {
                    status = AWS_IOT_JOB_STATE_FAILED;
                }
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Process a Job received from the Notify Next callback.
 *
 * @param[in] pJobInfo The parameter to the Notify Next callback that contains
 * information about the received Job.
 * @param[in] pJobId A pointer to the Job ID.
 * @param[in] jobIdLength The length of the Job ID.
 * @param[in] pJobDoc A pointer to the Job document.
 * @param[in] jobDocLength The length of the Job document.
 */
static void _processJob( const AwsIotJobsCallbackParam_t * pJobInfo,
                         const char * pJobId,
                         size_t jobIdLength,
                         const char * pJobDoc,
                         size_t jobDocLength )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_SUCCESS;
    AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    const char * pAction = NULL;
    size_t actionLength = 0;
    _jobAction_t action = JOB_ACTION_UNKNOWN;

    IotLogInfo( "Job document received: %.*s", jobDocLength, pJobDoc );

    /* Initialize the common parameter of Jobs requests. */
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;

    requestInfo.mqttConnection = pJobInfo->mqttConnection;
    requestInfo.pThingName = pJobInfo->pThingName;
    requestInfo.thingNameLength = pJobInfo->thingNameLength;
    requestInfo.pJobId = pJobId;
    requestInfo.jobIdLength = jobIdLength;

    /* Tell the Jobs service that the device has started working on the Job.
     * Use the StartNext API to set the Job's status to IN_PROGRESS. */
    callbackInfo.function = _operationCompleteCallback;

    status = AwsIotJobs_StartNextAsync( &requestInfo, &updateInfo, 0, &callbackInfo, NULL );

    IotLogInfo( "Jobs StartNext queued with result %s.", AwsIotJobs_strerror( status ) );

    /* Get the action for this device. */
    if( _getJsonString( pJobDoc,
                        jobDocLength,
                        JOB_ACTION_KEY,
                        JOB_ACTION_KEY_LENGTH,
                        &pAction,
                        &actionLength ) == true )
    {
        action = _getAction( pAction, actionLength );

        switch( action )
        {
            case JOB_ACTION_EXIT:
                callbackInfo.pCallbackContext = JOBS_DEMO_SHOULD_EXIT;
                updateInfo.newStatus = AWS_IOT_JOB_STATE_SUCCEEDED;
                break;

            case JOB_ACTION_PRINT:
            case JOB_ACTION_PUBLISH:
                updateInfo.newStatus = _processMessage( pJobInfo->mqttConnection,
                                                        action,
                                                        pJobDoc,
                                                        jobDocLength );
                break;

            default:
                IotLogError( "Received Job document with unknown action %.*s.",
                             actionLength,
                             pAction );

                updateInfo.newStatus = AWS_IOT_JOB_STATE_FAILED;
                break;
        }
    }
    else
    {
        IotLogError( "Received Job document does not contain an %s key.",
                     JOB_ACTION_KEY );

        /* The given Job document is not valid for this demo. */
        updateInfo.newStatus = AWS_IOT_JOB_STATE_FAILED;
    }

    IotLogInfo( "Setting state of %.*s to %s.",
                jobIdLength,
                pJobId,
                AwsIotJobs_StateName( updateInfo.newStatus ) );

    /* Tell the Jobs service that the device has finished the Job. */
    status = AwsIotJobs_UpdateAsync( &requestInfo, &updateInfo, 0, &callbackInfo, NULL );

    IotLogInfo( "Jobs Update queued with result %s.", AwsIotJobs_strerror( status ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Jobs Notify Next callback. This function is invoked when a new Job is
 * received from the Jobs service.
 *
 * @param[in] pCallbackContext Ignored.
 * @param[in] pCallbackInfo Contains the received Job.
 */
static void _jobsCallback( void * pCallbackContext,
                           AwsIotJobsCallbackParam_t * pCallbackInfo )
{
    /* Flags to track the contents of the received Job document. */
    bool idKeyFound = false, docKeyFound = false;

    /* The Job ID and length */
    const char * pJobId = NULL;
    size_t jobIdLength = 0;

    /* The Job document (which contains the action) and length. */
    const char * pJobDoc = NULL;
    size_t jobDocLength = 0;

    /* Silence warnings about unused parameters. */
    ( void ) pCallbackContext;

    /* Get the Job ID. */
    idKeyFound = _getJsonString( pCallbackInfo->u.callback.pDocument,
                                 pCallbackInfo->u.callback.documentLength,
                                 JOB_ID_KEY,
                                 JOB_ID_KEY_LENGTH,
                                 &pJobId,
                                 &jobIdLength );

    if( idKeyFound == true )
    {
        if( jobIdLength > JOB_ID_MAX_LENGTH )
        {
            IotLogError( "Received Job ID %.*s longer than %lu, which is the "
                         "maximum allowed by AWS IoT. Ignoring Job.",
                         jobIdLength,
                         pJobId,
                         ( unsigned long ) JOB_ID_MAX_LENGTH );

            idKeyFound = false;
        }
        else
        {
            IotLogInfo( "Job %.*s received.", jobIdLength, pJobId );
        }
    }

    /* Get the Job document.
     *
     * Note: This parser used is specific for parsing AWS IoT document received
     * through a mutually aithenticated connection. This parser will not check
     * for the correctness of the document as it is designed for low memory
     * footprint rather than checking for correctness of the document. This
     * parser is not meant to be used as a general purpose JSON parser.
     */
    docKeyFound = AwsIotDocParser_FindValue( pCallbackInfo->u.callback.pDocument,
                                             pCallbackInfo->u.callback.documentLength,
                                             JOB_DOC_KEY,
                                             JOB_DOC_KEY_LENGTH,
                                             &pJobDoc,
                                             &jobDocLength );

    /* When both the Job ID and Job document are available, process the Job. */
    if( ( idKeyFound == true ) && ( docKeyFound == true ) )
    {
        /* Process the Job document. */
        _processJob( pCallbackInfo,
                     pJobId,
                     jobIdLength,
                     pJobDoc,
                     jobDocLength );
    }
    else
    {
        /* The Jobs service sends an empty Job document when all Jobs are complete. */
        if( ( idKeyFound == false ) && ( docKeyFound == false ) )
        {
            IotLog( IOT_LOG_INFO, &_logHideAll,
                    "\r\n"
                    "/*-----------------------------------------------------------*/\r\n"
                    "\r\n"
                    "All available Jobs complete.\r\n"
                    "\r\n"
                    "/*-----------------------------------------------------------*/\r\n"
                    "\r\n" );
        }
        else
        {
            IotLogWarn( "Received an invalid Job document: %.*s",
                        pCallbackInfo->u.callback.documentLength,
                        pCallbackInfo->u.callback.pDocument );
        }
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief The function that runs the Jobs demo, called by the demo runner.
 *
 * @param[in] awsIotMqttMode Ignored for the Jobs demo.
 * @param[in] pIdentifier NULL-terminated Jobs Thing Name.
 * @param[in] pNetworkServerInfo Passed to the MQTT connect function when
 * establishing the MQTT connection for Jobs.
 * @param[in] pNetworkCredentialInfo Passed to the MQTT connect function when
 * establishing the MQTT connection for Jobs.
 * @param[in] pNetworkInterface The network interface to use for this demo.
 *
 * @return `EXIT_SUCCESS` if the demo completes successfully; `EXIT_FAILURE` otherwise.
 */
int RunJobsDemo( bool awsIotMqttMode,
                 const char * pIdentifier,
                 void * pNetworkServerInfo,
                 void * pNetworkCredentialInfo,
                 const IotNetworkInterface_t * pNetworkInterface )
{
    /* Return value of this function and the exit status of this program. */
    int status = EXIT_SUCCESS;

    /* Handle of the MQTT connection used in this demo. */
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

    /* Length of Jobs Thing Name. */
    size_t thingNameLength = 0;

    /* The function that will be set as the Jobs Notify Next callback. */
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;

    /* Status returned by the functions to set the Notify Next callback. */
    AwsIotJobsError_t callbackStatus = AWS_IOT_JOBS_SUCCESS;

    /* Flags for tracking which cleanup functions must be called. */
    bool initialized = false, connected = false;

    /* The first parameter of this demo function is not used. Jobs are specific
     * to AWS IoT, so this value is hardcoded to true whenever needed. */
    ( void ) awsIotMqttMode;

    /* Determine the length of the Thing Name. */
    if( pIdentifier != NULL )
    {
        thingNameLength = strlen( pIdentifier );

        if( thingNameLength == 0 )
        {
            IotLogError( "The length of the Thing Name (identifier) must be nonzero." );

            status = EXIT_FAILURE;
        }
    }
    else
    {
        IotLogError( "A Thing Name (identifier) must be provided for the Jobs demo." );

        status = EXIT_FAILURE;
    }

    /* Initialize the libraries required for this demo. */
    if( status == EXIT_SUCCESS )
    {
        status = _initializeDemo();

        if( status == EXIT_SUCCESS )
        {
            initialized = true;
        }
    }

    /* Establish the MQTT connection used in this demo. */
    if( status == EXIT_SUCCESS )
    {
        status = _establishMqttConnection( pIdentifier,
                                           pNetworkServerInfo,
                                           pNetworkCredentialInfo,
                                           pNetworkInterface,
                                           &mqttConnection );

        if( status == EXIT_SUCCESS )
        {
            connected = true;
        }
    }

    /* Set the Jobs Notify Next callback. This callback waits for the next available Job. */
    if( status == EXIT_SUCCESS )
    {
        callbackInfo.function = _jobsCallback;

        callbackStatus = AwsIotJobs_SetNotifyNextCallback( mqttConnection,
                                                           pIdentifier,
                                                           thingNameLength,
                                                           0,
                                                           &callbackInfo );

        IotLogInfo( "Jobs NotifyNext callback for %.*s set with result %s.",
                    thingNameLength,
                    pIdentifier,
                    AwsIotJobs_strerror( callbackStatus ) );

        if( callbackStatus != AWS_IOT_JOBS_SUCCESS )
        {
            status = EXIT_FAILURE;
        }
    }

    /* Wait for incoming Jobs. */
    if( status == EXIT_SUCCESS )
    {
        IotLog( IOT_LOG_INFO, &_logHideAll,
                "\r\n"
                "/*-----------------------------------------------------------*/\r\n"
                "\r\n"
                "The Jobs demo is now ready to accept Jobs.\r\n"
                "Jobs may be created using the AWS IoT console or AWS CLI.\r\n"
                "See the following link for more information.\r\n"
                "\r\n"
                "https://docs.aws.amazon.com/cli/latest/reference/iot/create-job.html\r\n"
                "\r\n"
                "This demo expects Job documents to have an \"action\" JSON key.\r\n"
                "The following actions are currently supported:\r\n"
                " - print\r\n"
                "   Logs a message to the local console. The Job document must also contain a \"message\".\r\n"
                "   For example: { \"action\": \"print\", \"message\": \"Hello world!\"} will cause\r\n"
                "   \"Hello world!\" to be printed on the console.\r\n"
                " - publish\r\n"
                "   Publishes a message to an MQTT topic. The Job document must also contain a \"message\" and \"topic\".\r\n"
                "   For example: { \"action\": \"publish\", \"topic\": \"demo/jobs\", \"message\": \"Hello world!\"} will cause\r\n"
                "   \"Hello world!\" to be published to the topic \"demo/jobs\".\r\n"
                " - exit\r\n"
                "   Exits the demo program. This program will run until { \"action\": \"exit\" } is received.\r\n"
                "\r\n"
                "/*-----------------------------------------------------------*/\r\n" );

        /* Wait until a Job with { "action": "exit" } is received. */
        while( Atomic_CompareAndSwap_u32( &_exitFlag, 0, JOBS_DEMO_FINISHED ) == 0 )
        {
            IotClock_SleepMs( 1000 );
        }
    }

    /* Remove the Jobs Notify Next callback. */
    if( status == EXIT_SUCCESS )
    {
        /* Specify that the _jobsCallback function should be replaced with NULL,
         * i.e. removed. */
        callbackInfo.function = NULL;
        callbackInfo.oldFunction = _jobsCallback;

        callbackStatus = AwsIotJobs_SetNotifyNextCallback( mqttConnection,
                                                           pIdentifier,
                                                           thingNameLength,
                                                           0,
                                                           &callbackInfo );

        IotLogInfo( "Jobs NotifyNext callback for %.*s removed with result %s.",
                    thingNameLength,
                    pIdentifier,
                    AwsIotJobs_strerror( callbackStatus ) );
    }

    /* Disconnect the MQTT connection and clean up the demo. */
    if( connected == true )
    {
        IotMqtt_Disconnect( mqttConnection, 0 );
    }

    if( initialized == true )
    {
        _cleanupDemo();
    }

    return status;
}

/*-----------------------------------------------------------*/
