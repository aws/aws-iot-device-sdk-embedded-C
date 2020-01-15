/*
* Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
*
* Licensed under the Apache License, Version 2.0 (the "License").
* You may not use this file except in compliance with the License.
* A copy of the License is located at
*
* http://aws.amazon.com/apache2.0
*
* or in the "license" file accompanying this file. This file is distributed
* on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
* express or implied. See the License for the specific language governing
* permissions and limitations under the License.
*/

#ifndef DISABLE_IOT_JOBS
#ifndef DISABLE_IOT_JOBS_INTERFACE

#include "aws_iot_test_integration_common.h"
#include <aws_iot_jobs_interface.h>
#include <aws_iot_jobs_json.h>
#include "aws_iot_download_agent.h"
#include "md5.h"
#include <inttypes.h>
#include <stdio.h>
#include <assert.h>
#include <fcntl.h>

static AWS_IoT_Client client;

static char jobId[MAX_SIZE_OF_JOB_ID] = {0};
static uint32_t fileSize = 0;
static uint32_t fileID = 0;
static char streamName[MAX_SIZE_OF_STREAM_NAME] = {0};
static void *pDownloadAgent = NULL;
static uint32_t downloadAgentSize = 0;
static uint32_t receivedFileSize = 0;
static char messageBuffer[MAX_SIZE_OF_JOB_REQUEST] = {0};
static bool stopDownloadAgentFlag = false;
static Timer requestTimer;
static char md5sum[33] = {0};

static jsmn_parser jsonParser;
static jsmntok_t jsonTokenStruct[MAX_JSON_TOKEN_EXPECTED] = {0};
static int32_t tokenCount;

static void aws_iot_mqtt_tests_disconnect_callback_handler(AWS_IoT_Client *pClient, void *param) {
}

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

				tokJobDocument = findToken("md5sum", pcJSON, tok);
				eResult = parseStringValue((char *) md5sum, 64, pcJSON, tokJobDocument);
				if(SUCCESS != eResult) {
					IOT_ERROR("parseStringValue returned error : %d ", eResult);
					eResult = FAILURE;
					break;
				}

				IOT_INFO("md5sum: %s", md5sum);
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

void iot_test_download_agent_get_pending_cb(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	IoT_Error_t rc = SUCCESS;
	char topicToPublishGetNext[MAX_JOB_TOPIC_LENGTH_BYTES];

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

	AwsIotDescribeJobExecutionRequest describeRequest;
	describeRequest.executionNumber = 0;
	describeRequest.includeJobDocument = true;
	describeRequest.clientToken = NULL;

	rc = aws_iot_jobs_describe(&client, QOS0, AWS_IOT_MY_THING_NAME, JOB_ID_NEXT, &describeRequest, topicToPublishGetNext, sizeof(topicToPublishGetNext), NULL, 0);
}

void iot_test_download_next_job_cb(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	char topicToPublishUpdate[MAX_JOB_TOPIC_LENGTH_BYTES];
	char messageBuffer[200];

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
			/* Alternatively if the job still has more steps the status can be set to JOB_EXECUTION_IN_PROGRESS instead */
			iot_update_job_status(pClient, (char *) jobId, JOB_EXECUTION_IN_PROGRESS, messageBuffer);
			countdown_ms(&requestTimer, AWS_IOT_DOWNLOAD_AGENT_REQUEST_WAIT_INTERVAL);
		}
	} else {
		IOT_INFO("execution property not found, nothing to do, jobs integration test complete");

		bool *testDone = (bool *) pData;
		*testDone = true;
	}
}

bool aws_iot_download_test_md5(void)
{
	bool ret = false;
	mbedtls_md5_context md5;
	uint8_t md5_calc[16] = {0};
	char md5str[33] = {0};
	char * binFile = NULL;
	int fd = 0;
	uint32_t ulBytes = 0;

	binFile = malloc(fileSize);
	if (NULL == binFile)
	{
		IOT_ERROR("Out of memory in md5sum check");
		return ret;
	}

	fd = open("mytest", O_RDWR, 0666);
	if (fd == -1)
	{
		IOT_ERROR("Cannot open test file");
		free(binFile);
		return ret;
	}

	lseek(fd, 0, SEEK_CUR);
	ulBytes = read(fd, binFile, fileSize);
	if (ulBytes != fileSize)
	{
		IOT_ERROR("Something wrong on read file, read size=%d, file size=%d", ulBytes, fileSize);
		free(binFile);
		return ret;
	}

	close(fd);

	mbedtls_md5_init(&md5);

	if ((ret = mbedtls_md5_starts_ret(&md5)) != 0)
		goto exit;
	if ((ret = mbedtls_md5_update_ret(&md5, (const unsigned char *) binFile, fileSize)) != 0)
		goto exit;
	if ((ret = mbedtls_md5_finish_ret(&md5, md5_calc)) != 0)
		goto exit;

	sprintf(md5str, "%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x%02x",
		md5_calc[0],md5_calc[1],md5_calc[2],md5_calc[3],
		md5_calc[4],md5_calc[5],md5_calc[6],md5_calc[7],
		md5_calc[8],md5_calc[9],md5_calc[10],md5_calc[11],
		md5_calc[12],md5_calc[13],md5_calc[14],md5_calc[15]);

	if (strcmp(md5sum, md5str) == 0)
	{
		IOT_INFO("md5sum check pass");
		ret = true;
	}

exit:
	mbedtls_md5_free(&md5);
	free(binFile);
	return ret;
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

int aws_iot_download_agent_basic_test() {
	char certDirectory[15] = "../../certs";
	char clientCRT[PATH_MAX + 1];
	char root_CA[PATH_MAX + 1];
	char clientKey[PATH_MAX + 1];
	char CurrentWD[PATH_MAX + 1];
	char clientId[50];
	char cPayload[100];
	IoT_Client_Init_Params initParams = IoT_Client_Init_Params_initializer;
	IoT_Client_Connect_Params connectParams;
	IoT_Publish_Message_Params paramsQOS0;
	IoT_Error_t rc = SUCCESS;
	struct timeval connectTime, waitCallBackTime;
	struct timeval start, end;
	unsigned int connectCounter = 0;

	IOT_DEBUG("\nConnecting Client ");
	do {
		getcwd(CurrentWD, sizeof(CurrentWD));
		snprintf(root_CA, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_ROOT_CA_FILENAME);
		snprintf(clientCRT, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_CERTIFICATE_FILENAME);
		snprintf(clientKey, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_PRIVATE_KEY_FILENAME);
		srand((unsigned int)time(NULL));
		snprintf(clientId, 50, "%s_%d", INTEGRATION_TEST_CLIENT_ID, rand() % 10000);

		printf("\n\nClient ID : %s \n", clientId);

		IOT_DEBUG("Root CA Path : %s\n clientCRT : %s\n clientKey : %s\n", root_CA, clientCRT, clientKey);
		initParams.pHostURL = AWS_IOT_MQTT_HOST;
		initParams.port = AWS_IOT_MQTT_PORT;
		initParams.pRootCALocation = root_CA;
		initParams.pDeviceCertLocation = clientCRT;
		initParams.pDevicePrivateKeyLocation = clientKey;
		initParams.mqttCommandTimeout_ms = 10000;
		initParams.tlsHandshakeTimeout_ms = 10000;
		initParams.disconnectHandler = aws_iot_mqtt_tests_disconnect_callback_handler;
		initParams.enableAutoReconnect = false;
		aws_iot_mqtt_init(&client, &initParams);

		connectParams.keepAliveIntervalInSec = 10;
		connectParams.isCleanSession = true;
		connectParams.MQTTVersion = MQTT_3_1_1;
		connectParams.pClientID = (char *)&clientId;
		connectParams.clientIDLen = strlen(clientId);
		connectParams.isWillMsgPresent = false;
		connectParams.pUsername = NULL;
		connectParams.usernameLen = 0;
		connectParams.pPassword = NULL;
		connectParams.passwordLen = 0;

		gettimeofday(&start, NULL);
		rc = aws_iot_mqtt_connect(&client, &connectParams);
		gettimeofday(&end, NULL);
		timersub(&end, &start, &connectTime);

		connectCounter++;
	} while(rc != SUCCESS && connectCounter < CONNECT_MAX_ATTEMPT_COUNT);

	if(SUCCESS == rc) {
		IOT_DEBUG("## Connect Success. Time sec: %ld, usec: %ld\n", (long int)connectTime.tv_sec, (long int)connectTime.tv_usec);
	} else {
		IOT_ERROR("## Connect Failed. error code %d\n", rc);
		return -1;
	}

	bool testDone = false;
	char topicToSubscribeGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeNotifyNext[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeGetNext[MAX_JOB_TOPIC_LENGTH_BYTES];

	char topicToPublishGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, NULL, JOB_GET_PENDING_TOPIC, JOB_WILDCARD_REPLY_TYPE,
		iot_test_download_agent_get_pending_cb, &testDone, topicToSubscribeGetPending, sizeof(topicToSubscribeGetPending));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_GET_PENDING_TOPIC: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, NULL, JOB_NOTIFY_NEXT_TOPIC, JOB_REQUEST_TYPE,
		iot_test_download_next_job_cb, &testDone, topicToSubscribeNotifyNext, sizeof(topicToSubscribeNotifyNext));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_NOTIFY_NEXT_TOPIC: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&client, QOS0, AWS_IOT_MY_THING_NAME, JOB_ID_NEXT, JOB_DESCRIBE_TOPIC, JOB_WILDCARD_REPLY_TYPE,
		iot_test_download_next_job_cb, &testDone, topicToSubscribeGetNext, sizeof(topicToSubscribeGetNext));

	if(SUCCESS != rc) {
		IOT_ERROR("Error subscribing JOB_DESCRIBE_TOPIC ($next): %d ", rc);
		return rc;
	}

	paramsQOS0.qos = QOS0;
	paramsQOS0.payload = (void *) cPayload;
	paramsQOS0.isRetained = 0;
	paramsQOS0.payloadLen = strlen(cPayload);

	rc = aws_iot_jobs_send_query(&client, QOS0, AWS_IOT_MY_THING_NAME, NULL, NULL, topicToPublishGetPending, sizeof(topicToPublishGetPending), NULL, 0, JOB_GET_PENDING_TOPIC);
	gettimeofday(&start, NULL);
	while (!testDone) {
		aws_iot_mqtt_yield(&client, 5000);

		gettimeofday(&end, NULL);
		timersub(&end, &start, &waitCallBackTime);

		if(waitCallBackTime.tv_sec > TIMEOUT_DOWNLOAD_FILE_SEC) break;

		if (NULL == pDownloadAgent)
		{
			// Not received job yet, download agent is not allocated.
			continue;
		}

		if (timerisset(&requestTimer.end_time) && has_timer_expired(&requestTimer) && (pDownloadAgent != NULL))
		{
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

			testDone = aws_iot_download_test_md5();
		}
	}

	if (testDone)
		return SUCCESS;
	else
		return FAILURE;
}

#endif
#endif
