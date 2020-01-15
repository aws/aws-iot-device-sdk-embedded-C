/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <fcntl.h>

#include "aws_iot_config.h"
#include "aws_iot_json_utils.h"
#include "aws_iot_log.h"
#include "aws_iot_version.h"
#include "aws_iot_mqtt_client_interface.h"
#include "aws_iot_jobs_interface.h"

#include "aws_iot_download_agent.h"

#define HOST_ADDRESS_SIZE 255

/**
 * @brief Default cert location
 */
static char certDirectory[PATH_MAX + 1] = "../../../certs";

/**
 * @brief Default MQTT HOST URL is pulled from the aws_iot_config.h
 */
static char HostAddress[HOST_ADDRESS_SIZE] = AWS_IOT_MQTT_HOST;

/**
 * @brief Default MQTT port is pulled from the aws_iot_config.h
 */
static uint32_t port = AWS_IOT_MQTT_PORT;

/**
 * @brief The job ID associated with this file from the job service
 */
static char jobId[MAX_SIZE_OF_JOB_ID] = {0};

/**
 * @brief The size of the file in bytes
 */
static uint32_t fileSize = 0;

/**
 * @brief The file is referenced by this numeric ID in the custom job.
 */
static uint32_t fileID = 0;

/**
 * @brief The stream associated with this file from the data block service
 */
static char streamName[MAX_SIZE_OF_STREAM_NAME] = {0};

/**
 * @brief Pointer to a block of memory for download agent use
 */
static void *pDownloadAgent = NULL;

/**
 * @brief Size of download agent memory
 */
static uint32_t downloadAgentSize = 0;

/**
 * @brief Received file size from download agent in bytes
 */
static uint32_t receivedFileSize = 0;

/**
 * @brief Buffer for job status detail message
 */
static char messageBuffer[MAX_SIZE_OF_JOB_REQUEST];

/**
 * @brief Flag to notify file download complete and stop agent
 */
static bool stopDownloadAgentFlag = false;

/**
 * @brief The request timer for restart the download agent
 */
static Timer requestTimer;

static jsmn_parser jsonParser;
static jsmntok_t jsonTokenStruct[MAX_JSON_TOKEN_EXPECTED];
static int32_t tokenCount;

/**
 * @brief Parse the download job document and validate.
 */
static IoT_Error_t iot_parse_job_doc(const char * pcJSON, uint32_t ulMsgLen)
{
	IoT_Error_t eResult = FAILURE;

	jsmn_init(&jsonParser);

	if(NULL == pcJSON || ulMsgLen <= 0) {
		IOT_ERROR("JSON is NULL pointer or payload size is = %d", ulMsgLen);
		return FAILURE;
	}

	tokenCount = jsmn_parse(&jsonParser, pcJSON, (int) ulMsgLen, jsonTokenStruct, MAX_JSON_TOKEN_EXPECTED);

	if(tokenCount < 0) {
		IOT_ERROR("Failed to parse JSON: %d", tokenCount);
		return FAILURE;
	}

	/* Assume the top-level element is an object */
	if(tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		IOT_ERROR("Top Level is not an object");
		return FAILURE;
	}

	jsmntok_t *tokExecution;

	tokExecution = findToken("execution", pcJSON, jsonTokenStruct);

	if (tokExecution) {
		IOT_INFO("execution: %.*s", tokExecution->end - tokExecution->start, (char *)pcJSON + tokExecution->start);

		do {
			jsmntok_t *tok;

			tok = findToken("jobId", pcJSON, tokExecution);

			if (tok) {
				eResult = parseStringValue((char *) jobId, MAX_SIZE_OF_JOB_ID + 1, pcJSON, tok);
				if(SUCCESS != eResult) {
					IOT_ERROR("parseStringValue returned error : %d ", eResult);
					eResult = FAILURE;
					break;
				}
			}

			IOT_INFO("jobId: %s", jobId);

			tok = findToken("jobDocument", pcJSON, tokExecution);

			if (tok) {
				jsmntok_t *tokJobDocument;

				tokJobDocument = findToken("streamId", pcJSON, tok);
				eResult = parseStringValue(streamName, MAX_SIZE_OF_STREAM_NAME + 1, pcJSON, tokJobDocument);
				if(SUCCESS != eResult) {
					IOT_ERROR("parseStringValue returned error : %d ", eResult);
					eResult = FAILURE;
					break;
				}

				IOT_INFO("streamId: %s", streamName);

				tokJobDocument = findToken("fileId", pcJSON, tok);
				eResult = parseUnsignedInteger32Value(&fileID, pcJSON, tokJobDocument);
				if(SUCCESS != eResult) {
					IOT_ERROR("parseStringValue returned error : %d ", eResult);
					eResult = FAILURE;
					break;
				}

				IOT_INFO("fileId: %d", fileID);

				tokJobDocument = findToken("fileSize", pcJSON, tok);
				eResult = parseUnsignedInteger32Value(&fileSize, pcJSON, tokJobDocument);
				if(SUCCESS != eResult) {
					IOT_ERROR("parseStringValue returned error : %d ", eResult);
					eResult = FAILURE;
					break;
				}

				IOT_INFO("fileSize: %d", fileSize);
				eResult = SUCCESS;
			}
		} while(0);
	} else {
		IOT_INFO("execution property not found, nothing to do");
		eResult = FAILURE;
	}

	return eResult;
}

static void iot_update_job_status(AWS_IoT_Client *pClient, char * jobId, JobExecutionStatus eStatus, const char * pcMsg) {
	char topicToPublishUpdate[MAX_JOB_TOPIC_LENGTH_BYTES];
	char messageBuffer[200];
	AwsIotJobExecutionUpdateRequest updateRequest;

	IoT_Error_t rc;

	updateRequest.status = eStatus;

	if (pcMsg)
		updateRequest.statusDetails = pcMsg;
	else
		updateRequest.statusDetails = "{\"reason\":\"UnknowException\"}";

	updateRequest.expectedVersion = 0;
	updateRequest.executionNumber = 0;
	updateRequest.includeJobExecutionState = false;
	updateRequest.includeJobDocument = false;
	updateRequest.clientToken = NULL;

	rc = aws_iot_jobs_send_update(pClient, QOS0, AWS_IOT_MY_THING_NAME, jobId, &updateRequest,
			topicToPublishUpdate, sizeof(topicToPublishUpdate), messageBuffer, sizeof(messageBuffer));
	if(SUCCESS != rc) {
		IOT_ERROR("aws_iot_jobs_send_update returned error : %d ", rc);
		return;
	}
}

static void iot_get_pending_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	IOT_INFO("\nJOB_GET_PENDING_TOPIC callback");
	IOT_INFO("topic: %.*s", topicNameLen, topicName);
	IOT_INFO("payload: %.*s", (int) params->payloadLen, (char *)params->payload);

	jsmn_init(&jsonParser);

	tokenCount = jsmn_parse(&jsonParser, params->payload, (int) params->payloadLen, jsonTokenStruct, MAX_JSON_TOKEN_EXPECTED);

	if(tokenCount < 0) {
		IOT_WARN("Failed to parse JSON: %d", tokenCount);
		return;
	}

	/* Assume the top-level element is an object */
	if(tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		IOT_WARN("Top Level is not an object");
		return;
	}

	jsmntok_t *jobs;

	jobs = findToken("inProgressJobs", params->payload, jsonTokenStruct);

	if (jobs) {
		IOT_INFO("inProgressJobs: %.*s", jobs->end - jobs->start, (char *)params->payload + jobs->start);
	}

	jobs = findToken("queuedJobs", params->payload, jsonTokenStruct);

	if (jobs) {
		IOT_INFO("queuedJobs: %.*s", jobs->end - jobs->start, (char *)params->payload + jobs->start);
	}
}

static void iot_next_job_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	IOT_INFO("\nJOB_NOTIFY_NEXT_TOPIC / JOB_DESCRIBE_TOPIC($next) callback");
	IOT_INFO("topic: %.*s", topicNameLen, topicName);
	IOT_INFO("payload: %.*s", (int) params->payloadLen, (char *)params->payload);

	jsmn_init(&jsonParser);

	tokenCount = jsmn_parse(&jsonParser, params->payload, (int) params->payloadLen, jsonTokenStruct, MAX_JSON_TOKEN_EXPECTED);

	if(tokenCount < 0) {
		IOT_WARN("Failed to parse JSON: %d", tokenCount);
		return;
	}

	/* Assume the top-level element is an object */
	if(tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		IOT_WARN("Top Level is not an object");
		return;
	}

	jsmntok_t *tokExecution;

	tokExecution = findToken("execution", params->payload, jsonTokenStruct);

	if (tokExecution) {
		IoT_Error_t rc;
		IOT_INFO("execution: %.*s", tokExecution->end - tokExecution->start, (char *)params->payload + tokExecution->start);
		/* Alternatively if the job still has more steps the status can be set to JOB_EXECUTION_IN_PROGRESS instead */
		rc = iot_parse_job_doc(params->payload, params->payloadLen);
		if ( SUCCESS != rc ) {
			strcpy(messageBuffer, "{\"reason\":\"InvalidJsonException\"}");
			iot_update_job_status(pClient, (char *) jobId, JOB_EXECUTION_FAILED, messageBuffer);
			return;
		}

		/*
		 * Do your job processing here.
		 */

		downloadAgentSize = aws_iot_download_agent_size(strlen(AWS_IOT_MY_THING_NAME), strlen(streamName), fileSize, MAX_SIZE_OF_FILE_BLOCK_LOG2);
		pDownloadAgent = malloc(downloadAgentSize);
		if (NULL == pDownloadAgent)
		{
			IOT_ERROR("Fail to allocate memory for download agent");
			strcpy(messageBuffer, "{\"reason\":\"OutOfMemoryException\"}");
			iot_update_job_status(pClient, (char *) jobId, JOB_EXECUTION_FAILED, messageBuffer);
			return;
		}

		memset(pDownloadAgent, 0, downloadAgentSize);

		rc = aws_iot_download_start(pClient,
							pDownloadAgent,
							downloadAgentSize,
							(uint8_t *) AWS_IOT_MY_THING_NAME,
							(uint8_t *) streamName,
							fileID,
							fileSize,
							MAX_SIZE_OF_FILE_BLOCK_LOG2,
							AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS);

		if( SUCCESS != rc )
		{
			IOT_ERROR( "Start download agent failed." );
			strcpy(messageBuffer, "{\"reason\":\"StartDownloadAgentException\"}");
			iot_update_job_status(pClient, (char *) jobId, JOB_EXECUTION_FAILED, messageBuffer);
			free(pDownloadAgent);
			pDownloadAgent = NULL;
			downloadAgentSize = 0;
		}
		else
		{
			IOT_INFO( "Start download agent success." );
			snprintf(messageBuffer, sizeof(messageBuffer),
									"{\"receive\":\"%u/%u\"}",
									receivedFileSize,
									fileSize);
			iot_update_job_status(pClient, (char *) jobId, JOB_EXECUTION_IN_PROGRESS, messageBuffer);
			countdown_ms(&requestTimer, AWS_IOT_DOWNLOAD_AGENT_REQUEST_WAIT_INTERVAL);
		}
	} else {
		IOT_INFO("execution property not found, nothing to do");
	}
}

static void iot_update_accepted_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	IOT_INFO("\nJOB_UPDATE_TOPIC / accepted callback");
	IOT_INFO("topic: %.*s", topicNameLen, topicName);
	IOT_INFO("payload: %.*s", (int) params->payloadLen, (char *)params->payload);
}

static void iot_update_rejected_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	IOT_INFO("\nJOB_UPDATE_TOPIC / rejected callback");
	IOT_INFO("topic: %.*s", topicNameLen, topicName);
	IOT_INFO("payload: %.*s", (int) params->payloadLen, (char *)params->payload);

	/* Do error handling here for when the update was rejected */
}

static void disconnectCallbackHandler(AWS_IoT_Client *pClient, void *data) {
	IOT_WARN("MQTT Disconnect");
	IoT_Error_t rc = FAILURE;

	if(NULL == pClient) {
		return;
	}

	IOT_UNUSED(data);

	if(aws_iot_is_autoreconnect_enabled(pClient)) {
		IOT_INFO("Auto Reconnect is enabled, Reconnecting attempt will start now");
	} else {
		IOT_WARN("Auto Reconnect not enabled. Starting manual reconnect...");
		rc = aws_iot_mqtt_attempt_reconnect(pClient);
		if(NETWORK_RECONNECTED == rc) {
			IOT_WARN("Manual Reconnect Successful");
		} else {
			IOT_WARN("Manual Reconnect Failed - %d", rc);
		}
	}
}

uint32_t aws_iot_download_save_block( uint8_t * pucStreamName,
									  uint32_t ulServerFileID,
									  uint32_t ulOffset,
									  uint8_t const * pcData,
									  uint32_t ulBlockSize,
									  uint32_t ulBlocksRemaining )
{
#if defined (__APPLE__) || (__linux__) || (__unix__)
	uint32_t ulBytes = 0;
	int fd = open("mytest", O_RDWR | O_CREAT, 0666);

	if (fd == -1)
	{
		IOT_ERROR("Cannot open test file");
		return ulBytes;
	}

	lseek( fd, ulOffset, SEEK_CUR );
	ulBytes = write(fd, pcData, ulBlockSize);

	close(fd);

	if (ulBytes != ulBlockSize)
	{
		IOT_INFO( "Something wrong on saving block, write size=%d, block size=%d", ulBytes, ulBlockSize );
		return ulBytes;
	}

	receivedFileSize += ulBlockSize;

	if (( ulBlocksRemaining <= 0 ) && (pDownloadAgent != NULL))
	{
		IOT_INFO( "All the blocks are complete download." );
		stopDownloadAgentFlag = true;
	}

	return ulBytes;
#else
	#error "Implement your write block code here!"
#endif
}

int main(int argc, char **argv) {
	char rootCA[PATH_MAX + 1];
	char clientCRT[PATH_MAX + 1];
	char clientKey[PATH_MAX + 1];
	char CurrentWD[PATH_MAX + 1];

	IoT_Error_t rc = FAILURE;

	AWS_IoT_Client client;
	IoT_Client_Init_Params mqttInitParams = iotClientInitParamsDefault;
	IoT_Client_Connect_Params connectParams = iotClientConnectParamsDefault;

	getcwd(CurrentWD, sizeof(CurrentWD));
	snprintf(rootCA, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_ROOT_CA_FILENAME);
	snprintf(clientCRT, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_CERTIFICATE_FILENAME);
	snprintf(clientKey, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_PRIVATE_KEY_FILENAME);

	IOT_DEBUG("rootCA %s", rootCA);
	IOT_DEBUG("clientCRT %s", clientCRT);
	IOT_DEBUG("clientKey %s", clientKey);

	mqttInitParams.enableAutoReconnect = false; // We enable this later below
	mqttInitParams.pHostURL = HostAddress;
	mqttInitParams.port = port;
	mqttInitParams.pRootCALocation = rootCA;
	mqttInitParams.pDeviceCertLocation = clientCRT;
	mqttInitParams.pDevicePrivateKeyLocation = clientKey;
	mqttInitParams.mqttCommandTimeout_ms = 20000;
	mqttInitParams.tlsHandshakeTimeout_ms = 5000;
	mqttInitParams.isSSLHostnameVerify = true;
	mqttInitParams.disconnectHandler = disconnectCallbackHandler;
	mqttInitParams.disconnectHandlerData = NULL;

	rc = aws_iot_mqtt_init(&client, &mqttInitParams);
	if(SUCCESS != rc) {
		IOT_ERROR("aws_iot_mqtt_init returned error : %d ", rc);
		return rc;
	}

	connectParams.keepAliveIntervalInSec = 600;
	connectParams.isCleanSession = true;
	connectParams.MQTTVersion = MQTT_3_1_1;
	connectParams.pClientID = AWS_IOT_MQTT_CLIENT_ID;
	connectParams.clientIDLen = (uint16_t) strlen(AWS_IOT_MQTT_CLIENT_ID);
	connectParams.isWillMsgPresent = false;

	IOT_INFO("Connecting...");
	rc = aws_iot_mqtt_connect(&client, &connectParams);
	if(SUCCESS != rc) {
		IOT_ERROR("Error(%d) connecting to %s:%d", rc, mqttInitParams.pHostURL, mqttInitParams.port);
		return rc;
	}
	/*
	 * Enable Auto Reconnect functionality. Minimum and Maximum time of Exponential backoff are set in aws_iot_config.h
	 *  #AWS_IOT_MQTT_MIN_RECONNECT_WAIT_INTERVAL
	 *  #AWS_IOT_MQTT_MAX_RECONNECT_WAIT_INTERVAL
	 */
	rc = aws_iot_mqtt_autoreconnect_set_status(&client, true);
	if(SUCCESS != rc) {
		IOT_ERROR("Unable to set Auto Reconnect to true - %d", rc);
		return rc;
	}

	char topicToSubscribeGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeNotifyNext[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeGetNext[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeUpdateAccepted[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeUpdateRejected[MAX_JOB_TOPIC_LENGTH_BYTES];

	char topicToPublishGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToPublishGetNext[MAX_JOB_TOPIC_LENGTH_BYTES];

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, NULL, JOB_GET_PENDING_TOPIC, JOB_WILDCARD_REPLY_TYPE,
		iot_get_pending_callback_handler, NULL, topicToSubscribeGetPending, sizeof(topicToSubscribeGetPending));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_GET_PENDING_TOPIC: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, NULL, JOB_NOTIFY_NEXT_TOPIC, JOB_REQUEST_TYPE,
		iot_next_job_callback_handler, NULL, topicToSubscribeNotifyNext, sizeof(topicToSubscribeNotifyNext));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_NOTIFY_NEXT_TOPIC: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, JOB_ID_NEXT, JOB_DESCRIBE_TOPIC, JOB_WILDCARD_REPLY_TYPE,
		iot_next_job_callback_handler, NULL, topicToSubscribeGetNext, sizeof(topicToSubscribeGetNext));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_DESCRIBE_TOPIC ($next): %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, JOB_ID_WILDCARD, JOB_UPDATE_TOPIC, JOB_ACCEPTED_REPLY_TYPE,
		iot_update_accepted_callback_handler, NULL, topicToSubscribeUpdateAccepted, sizeof(topicToSubscribeUpdateAccepted));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_UPDATE_TOPIC/accepted: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, JOB_ID_WILDCARD, JOB_UPDATE_TOPIC, JOB_REJECTED_REPLY_TYPE,
		iot_update_rejected_callback_handler, NULL, topicToSubscribeUpdateRejected, sizeof(topicToSubscribeUpdateRejected));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_UPDATE_TOPIC/rejected: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_send_query(&client, QOS0, AWS_IOT_MY_THING_NAME, NULL, NULL, topicToPublishGetPending, sizeof(topicToPublishGetPending), NULL, 0, JOB_GET_PENDING_TOPIC);

	AwsIotDescribeJobExecutionRequest describeRequest;
	describeRequest.executionNumber = 0;
	describeRequest.includeJobDocument = true;
	describeRequest.clientToken = NULL;

	rc = aws_iot_jobs_describe(&client, QOS0, AWS_IOT_MY_THING_NAME, JOB_ID_NEXT, &describeRequest, topicToPublishGetNext, sizeof(topicToPublishGetNext), NULL, 0);

	init_timer(&requestTimer);

	for( ; ; )
	{
		//Max time the yield function will wait for read messages
		rc = aws_iot_mqtt_yield(&client, 100);
		if(NETWORK_ATTEMPTING_RECONNECT == rc) {
			// If the client is attempting to reconnect we will skip the rest of the loop.
			continue;
		}

		if (NULL == pDownloadAgent)
		{
			// Not received job yet, download agent is not allocated.
			continue;
		}

		if (timerisset(&requestTimer.end_time) && has_timer_expired(&requestTimer) && (pDownloadAgent != NULL))
		{
			// Since the first start of this download session in iot_next_job_callback_handler,
			// a certain period of time has elapsed, but the session hasn't finished downloading
			// all blocks of the file. Refresh the session by simply re-invoking aws_iot_download_start
			// with the same parameters. This will cause the agent to re-request the remaining
			// blocks. It will not re-download the already-downloaded blocks.
			IOT_INFO("Not download complete yet, restart agent.");

			rc = aws_iot_download_start(&client,
								pDownloadAgent,
								downloadAgentSize,
								(uint8_t *) AWS_IOT_MY_THING_NAME,
								(uint8_t *) streamName,
								fileID,
								fileSize,
								MAX_SIZE_OF_FILE_BLOCK_LOG2,
								AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS);

			if(rc != SUCCESS)
			{
				IOT_ERROR("Start download agent fail.");
				strcpy(messageBuffer, "{\"reason\":\"StartDownloadAgentException\"}");
				iot_update_job_status(&client, (char *) jobId, JOB_EXECUTION_FAILED, messageBuffer);

				(void) aws_iot_download_stop(&client, pDownloadAgent);
				free(pDownloadAgent);
				pDownloadAgent = NULL;
				downloadAgentSize = 0;
			}
			else
			{
				snprintf(messageBuffer, sizeof(messageBuffer),
										"{\"receive\":\"%u/%u\"}",
										receivedFileSize,
										fileSize);

				iot_update_job_status(&client, (char *) jobId, JOB_EXECUTION_IN_PROGRESS, messageBuffer);
			}

			countdown_ms(&requestTimer, AWS_IOT_DOWNLOAD_AGENT_REQUEST_WAIT_INTERVAL);
		}

		if ((stopDownloadAgentFlag) && (pDownloadAgent != NULL))
		{
			rc = aws_iot_download_stop(&client, pDownloadAgent);

			if(rc == SUCCESS)
			{
				IOT_INFO("Stop download agent success.");
				snprintf(messageBuffer, sizeof(messageBuffer),
										"{\"reason\":\"Success %ubytes\"}",
										receivedFileSize);
				iot_update_job_status(&client, (char *) jobId, JOB_EXECUTION_SUCCEEDED, messageBuffer);
			}
			else
			{
				IOT_ERROR("Stop download agent fail, force shutdown.");
				strcpy(messageBuffer, "{\"reason\":\"StopDownloadAgentException\"}");
				iot_update_job_status(&client, (char *) jobId, JOB_EXECUTION_FAILED, messageBuffer);
			}
			free(pDownloadAgent);
			pDownloadAgent = NULL;
			downloadAgentSize = 0;
			stopDownloadAgentFlag = false;
		}
	}

	return rc;
}
