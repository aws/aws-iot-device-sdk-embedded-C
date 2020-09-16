/*
 * FreeRTOS OTA V1.2.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file aws_iot_ota_mqtt.c
 * @brief Routines for supporting over the air updates using MQTT.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* MQTT includes. */
#include "mqtt.h"

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_internal.h"
#include "aws_iot_ota_cbor.h"

/* Include firmware version struct definition. */
#include "iot_appversion32.h"
extern  const AppVersion32_t xAppFirmwareVersion;

/* General constants. */
#define OTA_SUBSCRIBE_WAIT_MS          30000UL
#define OTA_UNSUBSCRIBE_WAIT_MS        1000UL
#define OTA_PUBLISH_WAIT_MS            10000UL
#define OTA_SUBSCRIBE_WAIT_TICKS       pdMS_TO_TICKS( OTA_SUBSCRIBE_WAIT_MS )
#define OTA_UNSUBSCRIBE_WAIT_TICKS     pdMS_TO_TICKS( OTA_UNSUBSCRIBE_WAIT_MS )
#define OTA_PUBLISH_WAIT_TICKS         pdMS_TO_TICKS( OTA_SUBSCRIBE_WAIT_TICKS )
#define OTA_MAX_PUBLISH_RETRIES        3                    /* Max number of publish retries */
#define OTA_RETRY_DELAY_MS             1000UL               /* Delay between publish retries */
#define U32_MAX_PLACES                 10U                  /* Maximum number of output digits of an unsigned long value. */
#define OTA_MAX_TOPIC_LEN              256U                 /* Max length of a dynamically generated topic string (usually on the stack). */

/* Stream GET message constants. */
#define OTA_CLIENT_TOKEN               "rdy"                /* Arbitrary client token sent in the stream "GET" message. */

/* Agent to Job Service status message constants. */
#define OTA_STATUS_MSG_MAX_SIZE        128U             /* Max length of a job status message to the service. */
#define OTA_UPDATE_STATUS_FREQUENCY    64U              /* Update the job status every 64 unique blocks received. */

/*lint -e830 -e9003 Keep these in one location for easy discovery should they change in the future. */
/* Topic strings used by the OTA process. */
/* These first few are topic extensions to the dynamic base topic that includes the Thing name. */
static const char pcOTA_JobsGetNextAccepted_TopicTemplate[] = "$aws/things/%s/jobs/$next/get/accepted";
static const char pcOTA_JobsNotifyNext_TopicTemplate[] = "$aws/things/%s/jobs/notify-next";
static const char pcOTA_JobsGetNext_TopicTemplate[] = "$aws/things/%s/jobs/$next/get";
static const char pcOTA_JobStatus_TopicTemplate[] = "$aws/things/%s/jobs/%s/update";
static const char pcOTA_StreamData_TopicTemplate[] = "$aws/things/%s/streams/%s/data/cbor";
static const char pcOTA_GetStream_TopicTemplate[] = "$aws/things/%s/streams/%s/get/cbor";
static const char pcOTA_GetNextJob_MsgTemplate[] = "{\"clientToken\":\"%u:%s\"}";
static const char pcOTA_JobStatus_StatusTemplate[] = "{\"status\":\"%s\",\"statusDetails\":{";
static const char pcOTA_JobStatus_ReceiveDetailsTemplate[] = "\"%s\":\"%u/%u\"}}";
static const char pcOTA_JobStatus_SelfTestDetailsTemplate[] = "\"%s\":\"%s\",\"" OTA_JSON_UPDATED_BY_KEY "\":\"0x%x\"}}";
static const char pcOTA_JobStatus_ReasonStrTemplate[] = "\"reason\":\"%s: 0x%08x\"}}";
static const char pcOTA_JobStatus_SucceededStrTemplate[] = "\"reason\":\"%s v%u.%u.%u\"}}";
static const char pcOTA_JobStatus_ReasonValTemplate[] = "\"reason\":\"0x%08x: 0x%08x\"}}";
static const char pcOTA_String_Receive[] = "receive";

/* We map all of the above status cases to one of these 4 status strings.
 * These are the only strings that are supported by the Job Service. You
 * shall not change them to arbitrary strings or the job will not change
 * states.
 * */
const char pcOTA_String_InProgress[] = "IN_PROGRESS";
const char pcOTA_String_Failed[] = "FAILED";
const char pcOTA_String_Succeeded[] = "SUCCEEDED";
const char pcOTA_String_Rejected[] = "REJECTED";

const char * pcOTA_JobStatus_Strings[ eNumJobStatusMappings ] =
{
    pcOTA_String_InProgress,
    pcOTA_String_Failed,
    pcOTA_String_Succeeded,
    pcOTA_String_Rejected,
    pcOTA_String_Failed, /* eJobStatus_FailedWithVal */
};

/* These are the associated statusDetails 'reason' codes that go along with
 * the above enums during the OTA update process. The 'Receiving' state is
 * updated with transfer progress as #blocks received of #total.
 */
const char * pcOTA_JobReason_Strings[ eNumJobReasons ] = { "", "ready", "active", "accepted", "rejected", "aborted" };

// /* Queue MQTT callback event for processing. */

// static void prvSendCallbackEvent( void * pvCallbackContext,
//                                   IotMqttCallbackParam_t * const pxPublishData,
//                                   OTA_Event_t xEventId );

// /* Called when a MQTT message is received on an OTA Job topic. */

// static void prvJobPublishCallback( void * pvCallbackContext,
//                                    IotMqttCallbackParam_t * const pxPublishData );

// /* Called when a MQTT message is received on an OTA data topic. */

// static void prvDataPublishCallback( void * pvCallbackContext,
//                                     IotMqttCallbackParam_t * const pxPublishData );

/* Subscribe to the jobs notification topic (i.e. New file version available). */

static bool prvSubscribeToJobNotificationTopics( const OTA_AgentContext_t * pxAgentCtx );

/* UnSubscribe from the firmware update receive topic. */

static bool prvUnSubscribeFromDataStream( const OTA_AgentContext_t * pxAgentCtx );

/* UnSubscribe from the jobs notification topic. */

static void prvUnSubscribeFromJobNotificationTopic( const OTA_AgentContext_t * pxAgentCtx );

/* Publish a message using the platforms PubSub mechanism. */

static MQTTStatus_t prvPublishMessage( const OTA_AgentContext_t * pxAgentCtx,
                                         const char * const pacTopic,
                                         uint16_t usTopicLen,
                                         const char * pcMsg,
                                         uint32_t ulMsgSize,
                                         MQTTQoS_t eQOS );

/* Subscribe to the OTA job notification topics. */

static bool prvSubscribeToJobNotificationTopics( const OTA_AgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvSubscribeToJobNotificationTopics" );

    bool bResult = false;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTContext_t * pMqttContext = pxAgentCtx->pvConnectionContext;
    MQTTSubscribeInfo_t subscriptionInfo;
    size_t subscriptionCount = 1;
    char pcJobTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t usTopicLen = 0;

    /* Build the first topic. */
    usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                        sizeof( pcJobTopic ),
                                        pcOTA_JobsGetNextAccepted_TopicTemplate,
                                        pxAgentCtx->pcThingName );

    /* Clear subscription struct and set common parameters for job topics used by OTA. */
    memset( &subscriptionInfo, 0, sizeof( subscriptionInfo ) );
    subscriptionInfo.qos = MQTTQoS1;
    subscriptionInfo.pTopicFilter = ( const char * ) pcJobTopic;
    subscriptionInfo.topicFilterLength = usTopicLen;

    if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        /* Subscribe to the first of two jobs topics. */
        mqttStatus = MQTT_Subscribe( pMqttContext,
                                     &subscriptionInfo,
                                     subscriptionCount,
                                     MQTT_GetPacketId( pMqttContext ) );


    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the subscription to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, OTA_SUBSCRIBE_WAIT_MS );
        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] Subscribe wait failed.\n\r", OTA_METHOD_NAME );
        }
    }


        if( mqttStatus == MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
            /* Build the second topic. */
            usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                                sizeof( pcJobTopic ),
                                                pcOTA_JobsNotifyNext_TopicTemplate,
                                                pxAgentCtx->pcThingName );
        }
        else
        {
            OTA_LOG_L1( "[%s] Failed: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
        }
    }

    if( ( mqttStatus == MQTTSuccess ) && ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        /* Subscribe to the second of two jobs topics. */
        subscriptionInfo.topicFilterLength = usTopicLen;
        mqttStatus = MQTT_Subscribe( pMqttContext,
                                     &subscriptionInfo,
                                     subscriptionCount,
                                     MQTT_GetPacketId( pMqttContext ) );

        if( mqttStatus == MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
            bResult = true;
        }
        else
        {
            OTA_LOG_L1( "[%s] Failed: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
        }
    }

    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the subscription to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, OTA_SUBSCRIBE_WAIT_MS );
        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] Subscribe wait failed.\n\r", OTA_METHOD_NAME );
        }
    }

    return bResult;
}

/*
 * UnSubscribe from the OTA data stream topic.
 */
static bool prvUnSubscribeFromDataStream( const OTA_AgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvUnSubscribeFromDataStream" );

    bool bResult = false;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTContext_t * pMqttContext = pxAgentCtx->pvConnectionContext;
    MQTTSubscribeInfo_t subscriptionInfo;
    size_t subscriptionCount = 1;

    char pcOTA_RxStreamTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t usTopicLen = 0;
    const OTA_FileContext_t * pFileContext = &( pxAgentCtx->pxOTA_Files[ pxAgentCtx->ulFileIndex ] );

    if( ( pFileContext != NULL ) && ( pFileContext->pucStreamName != NULL ) )
    {
        /* Try to build the dynamic data stream topic. */
        usTopicLen = ( uint16_t ) snprintf( pcOTA_RxStreamTopic,
                                            sizeof( pcOTA_RxStreamTopic ),
                                            pcOTA_StreamData_TopicTemplate,
                                            pxAgentCtx->pcThingName,
                                            ( const char * ) pFileContext->pucStreamName );

        /* Clear subscription struct and set common parameters for job topics used by OTA. */
        memset( &subscriptionInfo, 0, sizeof( subscriptionInfo ) );
        subscriptionInfo.qos = MQTTQoS0;
        subscriptionInfo.pTopicFilter = ( const char * ) pcOTA_RxStreamTopic;
        subscriptionInfo.topicFilterLength = usTopicLen;

        if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcOTA_RxStreamTopic ) ) )
        {
            mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                        &subscriptionInfo,
                                        subscriptionCount,
                                        MQTT_GetPacketId( pMqttContext ) );

            if( mqttStatus == MQTTSuccess )
            {
                OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
            }
            else
            {
                OTA_LOG_L1( "[%s] FAIL: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Failed to build stream topic.\n\r", OTA_METHOD_NAME );
        }
    }

    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the unsubscription to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, OTA_UNSUBSCRIBE_WAIT_MS );
        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] Unsubscribe wait failed.\n\r", OTA_METHOD_NAME );
        }
    }

    return bResult;
}

/*
 * Unsubscribe from the OTA job notification topics.
 */
static void prvUnSubscribeFromJobNotificationTopic( const OTA_AgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvUnSubscribeFromJobNotificationTopic" );

    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = pxAgentCtx->pvConnectionContext;
    MQTTSubscribeInfo_t subscriptionInfo;
    size_t subscriptionCount = 1;
    char pcJobTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t usTopicLen = 0;

    /* Build the first topic. */
    usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                        sizeof( pcJobTopic ),
                                        pcOTA_JobsNotifyNext_TopicTemplate,
                                        pxAgentCtx->pcThingName );

    /* Clear subscription struct and set common parameters for job topics used by OTA. */
    memset( &subscriptionInfo, 0, sizeof( subscriptionInfo ) );
    subscriptionInfo.qos = MQTTQoS0;
    subscriptionInfo.pTopicFilter = ( const char * ) pcJobTopic;
    subscriptionInfo.topicFilterLength = usTopicLen;

    if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        /* Unsubscribe to the first of two jobs topics. */
        mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                       &subscriptionInfo,
                                       subscriptionCount,
                                       MQTT_GetPacketId( pMqttContext ));
        if( mqttStatus == MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
            /* Build the second topic. */
            usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                                sizeof( pcJobTopic ),
                                                pcOTA_JobsGetNextAccepted_TopicTemplate,
                                                pxAgentCtx->pcThingName );
        }
        else
        {
            OTA_LOG_L1( "[%s] Failed: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
        }
    }

    if( ( mqttStatus == MQTTSuccess ) && ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        /* Unsubscribe from the second of two jobs topics. */
        subscriptionInfo.topicFilterLength = usTopicLen;
        mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                       &subscriptionInfo,
                                       subscriptionCount,
                                       MQTT_GetPacketId( pMqttContext ) );
        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] Failed: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
        }
        else
        {
            OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, subscriptionInfo.pTopicFilter );
        }
    }

    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the unsubscription to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, OTA_UNSUBSCRIBE_WAIT_MS );
        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] Unsubscribe wait failed.\n\r", OTA_METHOD_NAME );
        }
    }
}

/*
 * Publish a message to the specified client/topic at the given QOS.
 */
static MQTTStatus_t prvPublishMessage( const OTA_AgentContext_t * pxAgentCtx,
                                         const char * const pacTopic,
                                         uint16_t usTopicLen,
                                         const char * pcMsg,
                                         uint32_t ulMsgSize,
                                         MQTTQoS_t eQOS )
{
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTPublishInfo_t publishInfo;
    MQTTContext_t * pMqttContext = pxAgentCtx->pvConnectionContext;

    publishInfo.pTopicName = pacTopic;
    publishInfo.topicNameLength = usTopicLen;
    publishInfo.qos = eQOS;
    publishInfo.pPayload = pcMsg;
    publishInfo.payloadLength = ulMsgSize;

    mqttStatus = MQTT_Publish( pMqttContext,
                               &publishInfo,
                               MQTT_GetPacketId( pMqttContext ) );

    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the publish to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, OTA_PUBLISH_WAIT_MS );
        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( " Publish ack wait failed.\n\r" );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Failed to send PUBLISH packet to broker with error = %u.", mqttStatus );
    }

    return mqttStatus;
}

/*
 * Publish a message to the job status topic.
 */
static void prvPublishStatusMessage( OTA_AgentContext_t * pxAgentCtx,
                                     OTA_JobStatus_t eStatus,
                                     const char * pcMsg,
                                     uint32_t ulMsgSize,
                                     MQTTQoS_t eQOS )
{
    DEFINE_OTA_METHOD_NAME( "prvPublishStatusMessage" );

    uint32_t ulTopicLen = 0;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    char pcTopicBuffer[ OTA_MAX_TOPIC_LEN ];

    /* Try to build the dynamic job status topic . */
    ulTopicLen = ( uint32_t ) snprintf( pcTopicBuffer, /*lint -e586 Intentionally using snprintf. */
                                        sizeof( pcTopicBuffer ),
                                        pcOTA_JobStatus_TopicTemplate,
                                        pxAgentCtx->pcThingName,
                                        pxAgentCtx->pcOTA_Singleton_ActiveJobName );

    /* If the topic name was built, try to publish the status message to it. */
    if( ( ulTopicLen > 0UL ) && ( ulTopicLen < sizeof( pcTopicBuffer ) ) )
    {
        OTA_LOG_L1( "[%s] Msg: %s\r\n", OTA_METHOD_NAME, pcMsg );
        mqttStatus = prvPublishMessage( pxAgentCtx,
                                        pcTopicBuffer,
                                        ( uint16_t ) ulTopicLen,
                                        &pcMsg[ 0 ],
                                        ulMsgSize,
                                        eQOS );

        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( "[%s] Failed: %s\r\n", OTA_METHOD_NAME, pcTopicBuffer );
        }
        else
        {
            OTA_LOG_L1( "[%s] '%s' to %s\r\n", OTA_METHOD_NAME, pcOTA_JobStatus_Strings[ eStatus ], pcTopicBuffer );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Failed to build job status topic!\r\n", OTA_METHOD_NAME );
    }
}

static uint32_t prvBuildStatusMessageReceiving( char * pcMsgBuffer,
                                                size_t xMsgBufferSize,
                                                OTA_JobStatus_t eStatus,
                                                OTA_FileContext_t * pxOTAFileCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvBuildStatusMessageReceiving" );

    uint32_t ulNumBlocks = 0;
    uint32_t ulReceived = 0;
    uint32_t ulMsgSize = 0;

    if( pxOTAFileCtx != NULL )
    {
        ulNumBlocks = ( pxOTAFileCtx->ulFileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        ulReceived = ulNumBlocks - pxOTAFileCtx->ulBlocksRemaining;

        if( ( ulReceived % OTA_UPDATE_STATUS_FREQUENCY ) == 0U ) /* Output a status update once in a while. */
        {
            ulMsgSize = ( uint32_t ) snprintf( pcMsgBuffer,      /*lint -e586 Intentionally using snprintf. */
                                               xMsgBufferSize,
                                               pcOTA_JobStatus_StatusTemplate,
                                               pcOTA_JobStatus_Strings[ eStatus ] );
            ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                                xMsgBufferSize - ulMsgSize,
                                                pcOTA_JobStatus_ReceiveDetailsTemplate,
                                                pcOTA_String_Receive,
                                                ulReceived,
                                                ulNumBlocks );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Error: null context pointer!\r\n", OTA_METHOD_NAME );
    }

    return ulMsgSize;
}

static uint32_t prvBuildStatusMessageSelfTest( char * pcMsgBuffer,
                                               size_t xMsgBufferSize,
                                               OTA_JobStatus_t eStatus,
                                               int32_t lReason )
{
    uint32_t ulMsgSize = 0;

    ulMsgSize = ( uint32_t ) snprintf( pcMsgBuffer, /*lint -e586 Intentionally using snprintf. */
                                       xMsgBufferSize,
                                       pcOTA_JobStatus_StatusTemplate,
                                       pcOTA_JobStatus_Strings[ eStatus ] );
    ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                        xMsgBufferSize - ulMsgSize,
                                        pcOTA_JobStatus_SelfTestDetailsTemplate,
                                        OTA_JSON_SELF_TEST_KEY,
                                        pcOTA_JobReason_Strings[ lReason ],
                                        xAppFirmwareVersion.u.ulVersion32 );

    return ulMsgSize;
}

static uint32_t prvBuildStatusMessageFinish( char * pcMsgBuffer,
                                             size_t xMsgBufferSize,
                                             OTA_JobStatus_t eStatus,
                                             int32_t lReason,
                                             int32_t lSubReason )
{
    uint32_t ulMsgSize = 0;

    ulMsgSize = ( uint32_t ) snprintf( pcMsgBuffer, /*lint -e586 Intentionally using snprintf. */
                                       xMsgBufferSize,
                                       pcOTA_JobStatus_StatusTemplate,
                                       pcOTA_JobStatus_Strings[ eStatus ] );

    /* FailedWithVal uses a numeric OTA error code and sub-reason code to cover the case where there
     * may be too many description strings to reasonably include in the code.
     */
    if( eStatus == eJobStatus_FailedWithVal )
    {
        ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                            xMsgBufferSize - ulMsgSize,
                                            pcOTA_JobStatus_ReasonValTemplate,
                                            lReason,
                                            lSubReason );
    }

    /* If the status update is for "Succeeded," we are identifying the version of firmware
     * that has been accepted. This makes it easy to find the version associated with each
     * device (aka Thing) when examining the OTA jobs on the service side via the CLI or
     * possibly with some console tool.
     */
    else if( eStatus == eJobStatus_Succeeded )
    {
        AppVersion32_t xNewVersion;

        xNewVersion.u.lVersion32 = lSubReason;
        ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                            xMsgBufferSize - ulMsgSize,
                                            pcOTA_JobStatus_SucceededStrTemplate,
                                            pcOTA_JobReason_Strings[ lReason ],
                                            xNewVersion.u.x.ucMajor,
                                            xNewVersion.u.x.ucMinor,
                                            xNewVersion.u.x.usBuild );
    }

    /* Status updates that are NOT "InProgress" or "Succeeded" or "FailedWithVal" map status and
     * reason codes to a string plus a sub-reason code.
     */
    else
    {
        ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                            xMsgBufferSize - ulMsgSize,
                                            pcOTA_JobStatus_ReasonStrTemplate,
                                            pcOTA_JobReason_Strings[ lReason ],
                                            lSubReason );
    }

    return ulMsgSize;
}

// /*
//  * This function queues callback events for processing.
//  */
// static void prvSendCallbackEvent( void * pvCallbackContext,
//                                   IotMqttCallbackParam_t * const pxPublishData,
//                                   OTA_Event_t xEventId )
// {
//     DEFINE_OTA_METHOD_NAME( "prvSendCallbackEvent" );
//     OTA_EventMsg_t xEventMsg = { 0 };
//     bool succeed = false;
//     OTA_EventData_t * pxData;

//     /* Get the OTA agent context. */
//     OTA_AgentContext_t * pxAgentCtx = ( OTA_AgentContext_t * ) pvCallbackContext;

//     if( pxPublishData->u.message.info.payloadLength <= OTA_DATA_BLOCK_SIZE )
//     {
//         /* Try to get OTA data buffer. */
//         pxData = prvOTAEventBufferGet();

//         if( pxData != NULL )
//         {
//             memcpy( pxData->ucData, pxPublishData->u.message.info.pPayload, pxPublishData->u.message.info.payloadLength );
//             pxData->ulDataLength = pxPublishData->u.message.info.payloadLength;
//             xEventMsg.xEventId = xEventId;
//             xEventMsg.pxEventData = pxData;

//             /* Send job document received event. */
//             succeed = OTA_SignalEvent( &xEventMsg );
//         }
//         else
//         {
//             OTA_LOG_L1( "Error: No OTA data buffers available.\r\n", OTA_DATA_BLOCK_SIZE );
//         }
//     }
//     else
//     {
//         OTA_LOG_L1( "Error: buffers are too small %d to contains the payload %d.\r\n", OTA_DATA_BLOCK_SIZE, pxPublishData->u.message.info.payloadLength );
//     }

//     if( succeed )
//     {
//         /* Update packet received statistics counter. */
//         pxAgentCtx->xStatistics.ulOTA_PacketsReceived++;
//     }
//     else
//     {
//         /* Update packet received statistics counter. */
//         pxAgentCtx->xStatistics.ulOTA_PacketsDropped++;
//     }
// }

// /*
//  * This function is called whenever we receive a Job MQTT publish message.
//  */
// static void prvJobPublishCallback( void * pvCallbackContext,
//                                    IotMqttCallbackParam_t * const pxPublishData )
// {
//     DEFINE_OTA_METHOD_NAME( "prvJobPublishCallback" );

//     /* Do nothing if this callback is invoked when the OTA agent is stopped. */
//     if( ( ( OTA_AgentContext_t * ) pvCallbackContext )->eState != eOTA_AgentState_Stopped )
//     {
//         /* Queue the event for processing job document. */
//         prvSendCallbackEvent( pvCallbackContext, pxPublishData, eOTA_AgentEvent_ReceivedJobDocument );
//     }
// }

// /*
//  * This function is called whenever we receive a data MQTT publish message.
//  */
// static void prvDataPublishCallback( void * pvCallbackContext,
//                                     IotMqttCallbackParam_t * const pxPublishData )
// {
//     DEFINE_OTA_METHOD_NAME( "prvDataPublishCallback" );

//     /* Do nothing if this callback is invoked when the OTA agent is stopped. */
//     if( ( ( OTA_AgentContext_t * ) pvCallbackContext )->eState != eOTA_AgentState_Stopped )
//     {
//         /* Queue the event for processing received file block. */
//         prvSendCallbackEvent( pvCallbackContext, pxPublishData, eOTA_AgentEvent_ReceivedFileBlock );
//     }
// }

/*
 * Check for next available OTA job from the job service by publishing
 * a "get next job" message to the job service.
 */

OTA_Err_t prvRequestJob_Mqtt( OTA_AgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvRequestJob_Mqtt" );

    char pcJobTopic[ OTA_MAX_TOPIC_LEN ];
    static uint32_t ulReqCounter = 0;
    MQTTStatus_t eResult;
    uint32_t ulMsgLen;
    uint16_t usTopicLen;
    OTA_Err_t xError = kOTA_Err_PublishFailed;

    /* The following buffer is big enough to hold a dynamically constructed $next/get job message.
     * It contains a client token that is used to track how many requests have been made. */
    char pcMsg[ CONST_STRLEN( pcOTA_GetNextJob_MsgTemplate ) + U32_MAX_PLACES + otaconfigMAX_THINGNAME_LEN ];

    /* Subscribe to the OTA job notification topic. */
    // if( prvSubscribeToJobNotificationTopics( pxAgentCtx ) )
    // {
    //     OTA_LOG_L1( "[%s] Request #%u\r\n", OTA_METHOD_NAME, ulReqCounter );
    //     /*lint -e586 Intentionally using snprintf. */
    //     ulMsgLen = ( uint32_t ) snprintf( pcMsg,
    //                                       sizeof( pcMsg ),
    //                                       pcOTA_GetNextJob_MsgTemplate,
    //                                       ulReqCounter,
    //                                       pxAgentCtx->pcThingName );
    //     ulReqCounter++;
    //     usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
    //                                         sizeof( pcJobTopic ),
    //                                         pcOTA_JobsGetNext_TopicTemplate,
    //                                         pxAgentCtx->pcThingName );

    //     if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    //     {
    //         eResult = prvPublishMessage( pxAgentCtx, pcJobTopic, usTopicLen, pcMsg, ulMsgLen, MQTTQoS1 );

    //         if( eResult != MQTTSuccess )
    //         {
    //             OTA_LOG_L1( "[%s] Failed to publish MQTT message.\r\n", OTA_METHOD_NAME );
    //             xError = kOTA_Err_PublishFailed;
    //         }
    //         else
    //         {
    //             /* Nothing special to do. We succeeded. */
    //             xError = kOTA_Err_None;
    //         }
    //     }
    //     else
    //     {
    //         OTA_LOG_L1( "[%s] Topic too large for supplied buffer.\r\n", OTA_METHOD_NAME );
    //         xError = kOTA_Err_TopicTooLarge;
    //     }
    // }

    return kOTA_Err_None;
}


/*
 * Update the job status on the service side with progress or completion info.
 */
OTA_Err_t prvUpdateJobStatus_Mqtt( OTA_AgentContext_t * pxAgentCtx,
                                   OTA_JobStatus_t eStatus,
                                   int32_t lReason,
                                   int32_t lSubReason )
{
    DEFINE_OTA_METHOD_NAME( "prvUpdateJobStatus_Mqtt" );

    /* A message size of zero means don't publish anything. */
    uint32_t ulMsgSize = 0;
    /* All job state transitions except streaming progress use QOS 1 since it is required to have status in the job document. */
    MQTTQoS_t eQOS = MQTTQoS1;
    char pcMsg[ OTA_STATUS_MSG_MAX_SIZE ];

    /* Get the current file context. */
    OTA_FileContext_t * C = &( pxAgentCtx->pxOTA_Files[ pxAgentCtx->ulFileIndex ] );

    if( eStatus == eJobStatus_InProgress )
    {
        if( lReason == ( int32_t ) eJobReason_Receiving )
        {
            ulMsgSize = prvBuildStatusMessageReceiving( pcMsg, sizeof( pcMsg ), eStatus, C );

            if( ulMsgSize > 0 )
            {
                /* Downgrade Progress updates to QOS 0 to avoid overloading MQTT buffers during active streaming. */
                eQOS = MQTTQoS0;
            }
        }
        else
        {
            /* We're no longer receiving but we're still In Progress so we are implicitly in the Self
             * Test phase. Prepare to update the job status with the self_test phase (ready or active). */
            ulMsgSize = prvBuildStatusMessageSelfTest( pcMsg, sizeof( pcMsg ), eStatus, lReason );
        }
    }
    else
    {
        if( eStatus < eNumJobStatusMappings )
        {
            ulMsgSize = prvBuildStatusMessageFinish( pcMsg, sizeof( pcMsg ), eStatus, lReason, lSubReason );
        }
        else
        {
            OTA_LOG_L1( "[%s] Unknown status code: %d\r\n", OTA_METHOD_NAME, eStatus );
        }
    }

    if( ulMsgSize > 0UL )
    {
        prvPublishStatusMessage( pxAgentCtx, eStatus, pcMsg, ulMsgSize, eQOS );
    }

    return kOTA_Err_None;
}

/*
 * Init file transfer by subscribing to the OTA data stream topic.
 */
// OTA_Err_t prvInitFileTransfer_Mqtt( OTA_AgentContext_t * pxAgentCtx )
// {
//     DEFINE_OTA_METHOD_NAME( "prvInitFileTransfer_Mqtt" );

//     OTA_Err_t xResult = kOTA_Err_PublishFailed;
//     MQTTStatus_t mqttStatus = MQTTBadParameter;
//     MQTTContext_t * pMqttContext = pxAgentCtx->pvConnectionContext;
//     MQTTSubscribeInfo_t xOTAUpdateDataSubscription;
//     size_t subscriptionCount = 1;

//     char pcOTA_RxStreamTopic[ OTA_MAX_TOPIC_LEN ];
//     uint16_t usTopicLen = 0;
//     const OTA_FileContext_t * pFileContext = &( pxAgentCtx->pxOTA_Files[ pxAgentCtx->ulFileIndex ] );

//     usTopicLen = ( uint16_t ) snprintf( pcOTA_RxStreamTopic,
//                                         sizeof( pcOTA_RxStreamTopic ),
//                                         pcOTA_StreamData_TopicTemplate,
//                                         pxAgentCtx->pcThingName,
//                                         ( const char * ) pFileContext->pucStreamName );

//     memset( &xOTAUpdateDataSubscription, 0, sizeof( xOTAUpdateDataSubscription ) );
//     xOTAUpdateDataSubscription.qos = MQTTQoS0;
//     xOTAUpdateDataSubscription.pTopicFilter = ( const char * ) pcOTA_RxStreamTopic;
//     xOTAUpdateDataSubscription.topicFilterLength = usTopicLen;

//     if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcOTA_RxStreamTopic ) ) )
//     {
//         mqttStatus = MQTT_Subscribe( pMqttContext,
//                                      &xOTAUpdateDataSubscription,
//                                      subscriptionCount,
//                                      MQTT_GetPacketId( pMqttContext ) );
//         if( mqttStatus != MQTTSuccess )
//         {
//             OTA_LOG_L1( "[%s] Failed: %s\n\r", OTA_METHOD_NAME, xOTAUpdateDataSubscription.pTopicFilter );
//         }
//         else
//         {
//             OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, xOTAUpdateDataSubscription.pTopicFilter );
//         }
//     }
//     else
//     {
//         OTA_LOG_L1( "[%s] Failed to build stream topic.\n\r", OTA_METHOD_NAME );
//     }

//     if( mqttStatus == MQTTSuccess )
//     {
//         /* Wait for the subscription to complete. */
//         mqttStatus = MQTT_ProcessLoop( pMqttContext, OTA_SUBSCRIBE_WAIT_MS );
//         if( mqttStatus != MQTTSuccess )
//         {
//             OTA_LOG_L1( "[%s] Subscribe wait failed.\n\r", OTA_METHOD_NAME );
//         }
//         else
//         {
//             xResult = kOTA_Err_None;
//         }
//     }

//     return xResult;
// }

/*
 * Request file block by publishing to the get stream topic.
 */
// OTA_Err_t prvRequestFileBlock_Mqtt( OTA_AgentContext_t * pxAgentCtx )
// {
//     DEFINE_OTA_METHOD_NAME( "prvRequestFileBlock_Mqtt" );

//     size_t xMsgSizeFromStream;
//     uint32_t ulNumBlocks, ulBitmapLen;
//     uint32_t ulMsgSizeToPublish = 0;
//     uint32_t ulTopicLen = 0;
//     MQTTStatus_t mqttStatus = MQTTBadParameter;
//     OTA_Err_t xErr = kOTA_Err_Uninitialized;
//     char pcMsg[ OTA_REQUEST_MSG_MAX_SIZE ];
//     char pcTopicBuffer[ OTA_MAX_TOPIC_LEN ];

//     /*
//      * Get the current file context.
//      */
//     OTA_FileContext_t * C = &( pxAgentCtx->pxOTA_Files[ pxAgentCtx->ulFileIndex ] );

//     /* Reset number of blocks requested. */
//     pxAgentCtx->ulNumOfBlocksToReceive = otaconfigMAX_NUM_BLOCKS_REQUEST;

//     if( C != NULL )
//     {
//         ulNumBlocks = ( C->ulFileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
//         ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

//         if( OTA_CBOR_Encode_GetStreamRequestMessage(
//                 ( uint8_t * ) pcMsg,
//                 sizeof( pcMsg ),
//                 &xMsgSizeFromStream,
//                 OTA_CLIENT_TOKEN,
//                 ( int32_t ) C->ulServerFileID,
//                 ( int32_t ) ( OTA_FILE_BLOCK_SIZE & 0x7fffffffUL ), /* Mask to keep lint happy. It's still a constant. */
//                 0,
//                 C->pucRxBlockBitmap,
//                 ulBitmapLen,
//                 otaconfigMAX_NUM_BLOCKS_REQUEST ) )
//         {
//             xErr = kOTA_Err_None;
//         }
//         else
//         {
//             OTA_LOG_L1( "[%s] CBOR encode failed.\r\n", OTA_METHOD_NAME );
//             xErr = kOTA_Err_FailedToEncodeCBOR;
//         }
//     }

//     if( xErr == kOTA_Err_None )
//     {
//         ulMsgSizeToPublish = ( uint32_t ) xMsgSizeFromStream;

//         /* Try to build the dynamic data REQUEST topic to publish to. */
//         ulTopicLen = ( uint32_t ) snprintf( pcTopicBuffer, /*lint -e586 Intentionally using snprintf. */
//                                             sizeof( pcTopicBuffer ),
//                                             pcOTA_GetStream_TopicTemplate,
//                                             pxAgentCtx->pcThingName,
//                                             ( const char * ) C->pucStreamName );

//         if( ( ulTopicLen > 0U ) && ( ulTopicLen < sizeof( pcTopicBuffer ) ) )
//         {
//             xErr = kOTA_Err_None;
//         }
//         else
//         {
//             /* 0 should never happen since we supply the format strings. It must be overflow. */
//             OTA_LOG_L1( "[%s] Failed to build stream topic!\r\n", OTA_METHOD_NAME );
//             xErr = kOTA_Err_TopicTooLarge;
//         }
//     }

//     if( xErr == kOTA_Err_None )
//     {
//         mqttStatus = prvPublishMessage( pxAgentCtx,
//                                         pcTopicBuffer,
//                                         ( uint16_t ) ulTopicLen,
//                                         &pcMsg[ 0 ],
//                                         ulMsgSizeToPublish,
//                                         MQTTQoS1 );

//         if( mqttStatus != MQTTSuccess )
//         {
//             OTA_LOG_L1( "[%s] Failed: %s\r\n", OTA_METHOD_NAME, pcTopicBuffer );
//             xErr = kOTA_Err_PublishFailed;
//         }
//         else
//         {
//             OTA_LOG_L1( "[%s] OK: %s\r\n", OTA_METHOD_NAME, pcTopicBuffer );
//             xErr = kOTA_Err_None;
//         }
//     }

//     return xErr;
// }

/*
 * Decode a cbor encoded fileblock received from streaming service.
 */
OTA_Err_t prvDecodeFileBlock_Mqtt( uint8_t * pucMessageBuffer,
                                   size_t xMessageSize,
                                   int32_t * plFileId,
                                   int32_t * plBlockId,
                                   int32_t * plBlockSize,
                                   uint8_t ** ppucPayload,
                                   size_t * pxPayloadSize )
{
    DEFINE_OTA_METHOD_NAME( "prvDecodeFileBlock_Mqtt" );
    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    /* Decode the CBOR content. */
    if( !OTA_CBOR_Decode_GetStreamResponseMessage(
            pucMessageBuffer,
            xMessageSize,
            plFileId,
            plBlockId,   /*lint !e9087 CBOR requires pointer to int and our block index's never exceed 31 bits. */
            plBlockSize, /*lint !e9087 CBOR requires pointer to int and our block sizes never exceed 31 bits. */
            ppucPayload, /* This payload gets malloc'd by OTA_CBOR_Decode_GetStreamResponseMessage(). We must free it. */
            pxPayloadSize ) )
    {
        xErr = kOTA_Err_GenericIngestError;
    }
    else
    {
        /* Decode the CBOR content. */
        memcpy( pucMessageBuffer, *ppucPayload, *pxPayloadSize );

        /* Free the payload as it is copied in data buffer. */
        free( *ppucPayload );
        *ppucPayload = pucMessageBuffer;

        xErr = kOTA_Err_None;
    }

    return xErr;
}

/*
 * Perform any cleanup operations required like unsubscribing from
 * job topics.
 */
OTA_Err_t prvCleanup_Mqtt( OTA_AgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvCleanup_Mqtt" );

    /* Unsubscribe from job notification topics. */
    prvUnSubscribeFromJobNotificationTopic( pxAgentCtx );

    /* Unsubscribe from data stream topics. */
    prvUnSubscribeFromDataStream( pxAgentCtx );

    return kOTA_Err_None;
}
