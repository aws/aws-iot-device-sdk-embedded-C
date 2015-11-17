/*
 * Copyright 2010-2015 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <limits.h>

#include "aws_iot_log.h"
#include "aws_iot_version.h"
#include "aws_iot_mqtt_interface.h"
#include "aws_iot_shadow_interface.h"
#include "aws_iot_config.h"

/**
 * @file shadow_console_echo.c
 * @brief  Echo received Delta message
 *
 * This application will echo the message received in delta, as reported.
 * for example:
 * Received Delta message
 * {
 *    "state": {
 *       "switch": "on"
 *   }
 * }
 * This delta message means the desired switch position has changed to "on"
 *
 * This application will take this delta message and publish it back as the reported message from the device.
 * {
 *    "state": {
 *     "reported": {
 *       "switch": "on"
 *      }
 *    }
 * }
 *
 * This update message will remove the delta that was created. If this message was not removed then the AWS IoT Thing Shadow is going to always have a delta and keep sending delta any time an update is applied to the Shadow
 * This example will not use any of the json builder/helper functions provided in the aws_iot_shadow_json_data.h.
 * @note Ensure the buffer sizes in aws_iot_config.h are big enough to receive the delta message. The delta message will also contain the metadata with the timestamps
 */

char certDirectory[PATH_MAX + 1] = "../../certs";
char HostAddress[255] = AWS_IOT_MQTT_HOST;
uint32_t port = AWS_IOT_MQTT_PORT;
bool messageArrivedOnDelta = false;

/*
 * @note The delta message is always sent on the "state" key in the json
 * @note Any time messages are bigger than AWS_IOT_MQTT_RX_BUF_LEN the underlying MQTT library will ignore it. The maximum size of the message that can be received is limited to the AWS_IOT_MQTT_RX_BUF_LEN
 */
char stringToEchoDelta[SHADOW_MAX_SIZE_OF_RX_BUFFER];

// Helper functions
void parseInputArgsForConnectParams(int argc, char** argv);

// Shadow Callback for receiving the delta
void DeltaCallback(const char *pJsonValueBuffer, uint32_t valueLength, jsonStruct_t *pJsonStruct_t);

void UpdateStatusCallback(const char *pThingName, ShadowActions_t action, Shadow_Ack_Status_t status,
		const char *pReceivedJsonDocument, void *pContextData);

int main(int argc, char** argv) {
	IoT_Error_t rc = NONE_ERROR;
	int32_t i = 0;

	char rootCA[PATH_MAX + 1];
	char clientCRT[PATH_MAX + 1];
	char clientKey[PATH_MAX + 1];
	char CurrentWD[PATH_MAX + 1];
	char cafileName[] = AWS_IOT_ROOT_CA_FILENAME;
	char clientCRTName[] = AWS_IOT_CERTIFICATE_FILENAME;
	char clientKeyName[] = AWS_IOT_PRIVATE_KEY_FILENAME;

	INFO("\nAWS IoT SDK Version %d.%d.%d-%s\n", VERSION_MAJOR, VERSION_MINOR, VERSION_PATCH, VERSION_TAG);

	getcwd(CurrentWD, sizeof(CurrentWD));
	sprintf(rootCA, "%s/%s/%s", CurrentWD, certDirectory, cafileName);
	sprintf(clientCRT, "%s/%s/%s", CurrentWD, certDirectory, clientCRTName);
	sprintf(clientKey, "%s/%s/%s", CurrentWD, certDirectory, clientKeyName);

	DEBUG("rootCA %s", rootCA);DEBUG("clientCRT %s", clientCRT);DEBUG("clientKey %s", clientKey);

	parseInputArgsForConnectParams(argc, argv);

	// initialize the mqtt client
	MQTTClient_t mqttClient;
	aws_iot_mqtt_init(&mqttClient);

	ShadowParameters_t sp = ShadowParametersDefault;
	sp.pMyThingName = AWS_IOT_MY_THING_NAME;
	sp.pMqttClientId = AWS_IOT_MQTT_CLIENT_ID;
	sp.pHost = AWS_IOT_MQTT_HOST;
	sp.port = AWS_IOT_MQTT_PORT;
	sp.pClientCRT = clientCRT;
	sp.pClientKey = clientKey;
	sp.pRootCA = rootCA;

	INFO("Shadow Init");
	rc = aws_iot_shadow_init(&mqttClient);
	if (NONE_ERROR != rc) {
		ERROR("Shadow Connection Error");
		return rc;
	}

	INFO("Shadow Connect");
	rc = aws_iot_shadow_connect(&mqttClient, &sp);
	if (NONE_ERROR != rc) {
		ERROR("Shadow Connection Error");
		return rc;
	}

	jsonStruct_t deltaObject;
	deltaObject.pData = stringToEchoDelta;
	deltaObject.pKey = "state";
	deltaObject.type = SHADOW_JSON_OBJECT;
	deltaObject.cb = DeltaCallback;

	/*
	 * Register the jsonStruct object
	 */
	rc = aws_iot_shadow_register_delta(&mqttClient, AWS_IOT_MY_THING_NAME, &deltaObject);

	// Now wait in the loop to receive any message sent from the console
	while (rc == NONE_ERROR) {
		/*
		 * Lets check for the incoming messages for 200 ms.
		 */
		rc = aws_iot_shadow_yield(&mqttClient, 200);

		if (messageArrivedOnDelta) {
			INFO("\nSending delta message back %s\n", stringToEchoDelta);
			rc = aws_iot_shadow_update(&mqttClient, AWS_IOT_MY_THING_NAME, stringToEchoDelta, UpdateStatusCallback, NULL, 2, true);
			messageArrivedOnDelta = false;
		}

		// sleep for some time in seconds
		sleep(1);
	}

	if (NONE_ERROR != rc) {
		ERROR("An error occurred in the loop %d", rc);
	}

	INFO("Disconnecting");
	rc = aws_iot_shadow_disconnect(&mqttClient);

	if (NONE_ERROR != rc) {
		ERROR("Disconnect error %d", rc);
	}

	return rc;
}
/**
 * @brief This function builds a full Shadow expected JSON document by putting the data in the reported section
 *
 * @param pJsonDocument Buffer to be filled up with the JSON data
 * @param maxSizeOfJsonDocument maximum size of the buffer that could be used to fill
 * @param pReceivedDeltaData This is the data that will be embedded in the reported section of the JSON document
 * @param lengthDelta Length of the data
 */
bool buildJSONForReported(char *pJsonDocument, size_t maxSizeOfJsonDocument, const char *pReceivedDeltaData, uint32_t lengthDelta) {
	int32_t ret;

	if (pJsonDocument == NULL) {
		return false;
	}

	char tempClientTokenBuffer[MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE];

	if(aws_iot_fill_with_client_token(tempClientTokenBuffer, MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE) != NONE_ERROR){
		return false;
	}

	ret = snprintf(pJsonDocument, maxSizeOfJsonDocument, "{\"state\":{\"reported\":%.*s}, \"clientToken\":\"%s\"}", lengthDelta, pReceivedDeltaData, tempClientTokenBuffer);

	if (ret >= maxSizeOfJsonDocument || ret < 0) {
		return false;
	}

	return true;
}

void parseInputArgsForConnectParams(int argc, char** argv) {
	int opt;

	while (-1 != (opt = getopt(argc, argv, "h:p:c:"))) {
		switch (opt) {
		case 'h':
			strcpy(HostAddress, optarg);
			DEBUG("Host %s", optarg);
			break;
		case 'p':
			port = atoi(optarg);
			DEBUG("arg %s", optarg);
			break;
		case 'c':
			strcpy(certDirectory, optarg);
			DEBUG("cert root directory %s", optarg);
			break;
		case '?':
			if (optopt == 'c') {
				ERROR("Option -%c requires an argument.", optopt);
			} else if (isprint(optopt)) {
				WARN("Unknown option `-%c'.", optopt);
			} else {
				WARN("Unknown option character `\\x%x'.", optopt);
			}
			break;
		default:
			ERROR("ERROR in command line argument parsing");
			break;
		}
	}

}


void DeltaCallback(const char *pJsonValueBuffer, uint32_t valueLength, jsonStruct_t *pJsonStruct_t) {

	DEBUG("Received Delta message %.*s", valueLength, pJsonValueBuffer);

	if (buildJSONForReported(stringToEchoDelta, SHADOW_MAX_SIZE_OF_RX_BUFFER, pJsonValueBuffer, valueLength)) {
		messageArrivedOnDelta = true;
	}
}

void UpdateStatusCallback(const char *pThingName, ShadowActions_t action, Shadow_Ack_Status_t status,
		const char *pReceivedJsonDocument, void *pContextData) {

	if (status == SHADOW_ACK_TIMEOUT) {
		INFO("Update Timeout--");
	} else if (status == SHADOW_ACK_REJECTED) {
		INFO("Update RejectedXX");
	} else if (status == SHADOW_ACK_ACCEPTED) {
		INFO("Update Accepted !!");
	}
}
