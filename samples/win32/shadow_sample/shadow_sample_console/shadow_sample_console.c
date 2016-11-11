/*
* Copyright 2010-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "targetver.h" 
#define WIN32_LEAN_AND_MEAN 
#include <windows.h>
#include <stdio.h>
#include <tchar.h>

#include "aws_iot_config.h"
#include "aws_iot_log.h"
#include "aws_iot_version.h"
#include "aws_iot_mqtt_client_interface.h"
#include "aws_iot_mqtt_client.h"
#include "aws_iot_shadow_interface.h"
#include "aws_iot_shadow_json_data.h"

#define ROOMTEMPERATURE_UPPERLIMIT 32.0f
#define ROOMTEMPERATURE_LOWERLIMIT 25.0f
#define STARTING_ROOMTEMPERATURE ROOMTEMPERATURE_LOWERLIMIT

#define MAX_LENGTH_OF_UPDATE_JSON_BUFFER 200

/*
*  Function prototypes
*/
static void simulateRoomTemperature(float *pRoomTemperature);
static void shadowUpdateStatusCallback(const char *pThingName, ShadowActions_t action, Shadow_Ack_Status_t status, const char *pReceivedJsonDocument, void *pContextData);
static void windowActuate_Callback(const char *pJsonString, uint32_t JsonStringDataLen, jsonStruct_t *pContext);

static AWS_IOT_SHADOW_INIT aws_iot_shadow_init_ptr = NULL;
static AWS_IOT_SHADOW_CONNECT aws_iot_shadow_connect_ptr = NULL;
static AWS_IOT_SHADOW_YIELD aws_iot_shadow_yield_ptr = NULL;
static AWS_IOT_SHADOW_DISCONNECT aws_iot_shadow_disconnect_ptr = NULL;
static AWS_IOT_SHADOW_UPDATE aws_iot_shadow_update_ptr = NULL;
static AWS_IOT_SHADOW_GET aws_iot_shadow_get_ptr = NULL;
static AWS_IOT_SHADOW_DELETE aws_iot_shadow_delete_ptr = NULL;
static AWS_IOT_SHADOW_REGISTER_DELTA aws_iot_shadow_register_delta_ptr = NULL;
static AWS_IOT_SHADOW_SET_AUTORECONNECT_STATUS aws_iot_shadow_set_autoreconnect_status_ptr = NULL;
static AWS_IOT_SHADOW_INIT_JSON_DOCUMENT aws_iot_shadow_init_json_document_ptr = NULL;
static AWS_IOT_SHADOW_ADD_DESIRED aws_iot_shadow_add_desired_ptr = NULL;
static AWS_IOT_SHADOW_ADD_REPORTED aws_iot_shadow_add_reported_ptr = NULL;
static AWS_IOT_FINALIZE_JSON_DOCUMENT aws_iot_finalize_json_document_ptr = NULL;

enum { PATH_MAX = 512 };

static char certDirectory[PATH_MAX + 1] = "..\\..\\..\\..\\certs";
static char HostAddress[255] = AWS_IOT_MQTT_HOST;
static uint32_t port = AWS_IOT_MQTT_PORT;
static uint8_t numPubs = 5;

int main()
{
	IoT_Error_t rc = FAILURE;
	int32_t i = 0;

	char JsonDocumentBuffer[MAX_LENGTH_OF_UPDATE_JSON_BUFFER];
	size_t sizeOfJsonDocumentBuffer = sizeof(JsonDocumentBuffer) / sizeof(JsonDocumentBuffer[0]);
	float temperature = 0.0;

	bool windowOpen = false;
	jsonStruct_t windowActuator;
	windowActuator.cb = windowActuate_Callback;
	windowActuator.pData = &windowOpen;
	windowActuator.pKey = "windowOpen";
	windowActuator.type = SHADOW_JSON_BOOL;

	jsonStruct_t temperatureHandler;
	temperatureHandler.cb = NULL;
	temperatureHandler.pKey = "temperature";
	temperatureHandler.pData = &temperature;
	temperatureHandler.type = SHADOW_JSON_FLOAT;

	char rootCA[PATH_MAX + 1];
	char clientCRT[PATH_MAX + 1];
	char clientKey[PATH_MAX + 1];
	char CurrentWD[PATH_MAX + 1];

	IOT_INFO("\nAWS IoT SDK Version %d.%d.%d-%s\n", VERSION_MAJOR, VERSION_MINOR, VERSION_PATCH, VERSION_TAG);

	GetCurrentDirectoryA(sizeof(CurrentWD), CurrentWD);
	snprintf(rootCA, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_ROOT_CA_FILENAME);
	snprintf(clientCRT, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_CERTIFICATE_FILENAME);
	snprintf(clientKey, PATH_MAX + 1, "%s/%s/%s", CurrentWD, certDirectory, AWS_IOT_PRIVATE_KEY_FILENAME);

	IOT_DEBUG("rootCA %s", rootCA);
	IOT_DEBUG("clientCRT %s", clientCRT);
	IOT_DEBUG("clientKey %s", clientKey);

	HMODULE hModule = LoadLibraryA("aws-iot-sdk.dll");

	aws_iot_shadow_init_ptr = (AWS_IOT_SHADOW_INIT)GetProcAddress(hModule, "aws_iot_shadow_init");;
	aws_iot_shadow_connect_ptr = (AWS_IOT_SHADOW_CONNECT)GetProcAddress(hModule, "aws_iot_shadow_connect");;
	aws_iot_shadow_yield_ptr = (AWS_IOT_SHADOW_YIELD)GetProcAddress(hModule, "aws_iot_shadow_yield");;
	aws_iot_shadow_disconnect_ptr = (AWS_IOT_SHADOW_DISCONNECT)GetProcAddress(hModule, "aws_iot_shadow_disconnect");;
	aws_iot_shadow_update_ptr = (AWS_IOT_SHADOW_UPDATE)GetProcAddress(hModule, "aws_iot_shadow_update");;
	aws_iot_shadow_get_ptr = (AWS_IOT_SHADOW_GET)GetProcAddress(hModule, "aws_iot_shadow_get");;
	aws_iot_shadow_delete_ptr = (AWS_IOT_SHADOW_DELETE)GetProcAddress(hModule, "aws_iot_shadow_delete");;
	aws_iot_shadow_register_delta_ptr = (AWS_IOT_SHADOW_REGISTER_DELTA)GetProcAddress(hModule, "aws_iot_shadow_register_delta");
	aws_iot_shadow_set_autoreconnect_status_ptr = (AWS_IOT_SHADOW_SET_AUTORECONNECT_STATUS)GetProcAddress(hModule, "aws_iot_shadow_set_autoreconnect_status");
	aws_iot_shadow_init_json_document_ptr = (AWS_IOT_SHADOW_INIT_JSON_DOCUMENT)GetProcAddress(hModule, "aws_iot_shadow_init_json_document");
	aws_iot_shadow_add_desired_ptr = (AWS_IOT_SHADOW_ADD_DESIRED)GetProcAddress(hModule, "aws_iot_shadow_add_desired");
	aws_iot_shadow_add_reported_ptr = (AWS_IOT_SHADOW_ADD_REPORTED)GetProcAddress(hModule, "aws_iot_shadow_add_reported");
	aws_iot_finalize_json_document_ptr = (AWS_IOT_FINALIZE_JSON_DOCUMENT)GetProcAddress(hModule, "aws_iot_finalize_json_document");

	// initialize the mqtt client
	AWS_IoT_Client mqttClient;

	ShadowInitParameters_t sp = ShadowInitParametersDefault;
	sp.pHost = AWS_IOT_MQTT_HOST;
	sp.port = AWS_IOT_MQTT_PORT;
	sp.pClientCRT = clientCRT;
	sp.pClientKey = clientKey;
	sp.pRootCA = rootCA;
	sp.enableAutoReconnect = false;
	sp.disconnectHandler = NULL;

	IOT_INFO("Shadow Init");
	rc = aws_iot_shadow_init_ptr(&mqttClient, &sp);
	if (SUCCESS != rc) {
		IOT_ERROR("Shadow Connection Error");
		return rc;
	}

	ShadowConnectParameters_t scp = ShadowConnectParametersDefault;
	scp.pMyThingName = AWS_IOT_MY_THING_NAME;
	scp.pMqttClientId = AWS_IOT_MQTT_CLIENT_ID;
	scp.mqttClientIdLen = (uint16_t)strlen(AWS_IOT_MQTT_CLIENT_ID);

	IOT_INFO("Shadow Connect");
	rc = aws_iot_shadow_connect_ptr(&mqttClient, &scp);
	if (SUCCESS != rc) {
		IOT_ERROR("Shadow Connection Error");
		return rc;
	}

	/*
	* Enable Auto Reconnect functionality. Minimum and Maximum time of Exponential backoff are set in aws_iot_config.h
	*  #AWS_IOT_MQTT_MIN_RECONNECT_WAIT_INTERVAL
	*  #AWS_IOT_MQTT_MAX_RECONNECT_WAIT_INTERVAL
	*/
	rc = aws_iot_shadow_set_autoreconnect_status_ptr(&mqttClient, true);
	if (SUCCESS != rc) {
		IOT_ERROR("Unable to set Auto Reconnect to true - %d", rc);
		return rc;
	}

	rc = aws_iot_shadow_register_delta_ptr(&mqttClient, &windowActuator);

	if (SUCCESS != rc) {
		IOT_ERROR("Shadow Register Delta Error");
	}
	temperature = STARTING_ROOMTEMPERATURE;

	// loop and publish a change in temperature
	while (NETWORK_ATTEMPTING_RECONNECT == rc || NETWORK_RECONNECTED == rc || SUCCESS == rc) {
		rc = aws_iot_shadow_yield_ptr(&mqttClient, 200);
		if (NETWORK_ATTEMPTING_RECONNECT == rc) {
			Sleep(1);
			// If the client is attempting to reconnect we will skip the rest of the loop.
			continue;
		}
		IOT_INFO("\n=======================================================================================\n");
		IOT_INFO("On Device: window state %s", windowOpen ? "true" : "false");
		simulateRoomTemperature(&temperature);

		rc = aws_iot_shadow_init_json_document_ptr(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
		if (SUCCESS == rc) {
			rc = aws_iot_shadow_add_reported_ptr(JsonDocumentBuffer, sizeOfJsonDocumentBuffer, 2, &temperatureHandler,
				&windowActuator);
			if (SUCCESS == rc) {
				rc = aws_iot_finalize_json_document_ptr(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
				if (SUCCESS == rc) {
					IOT_INFO("Update Shadow: %s", JsonDocumentBuffer);
					rc = aws_iot_shadow_update_ptr(&mqttClient, AWS_IOT_MY_THING_NAME, JsonDocumentBuffer, shadowUpdateStatusCallback, NULL, 4, true);
				}
			}
		}
		IOT_INFO("*****************************************************************************************\n");
		Sleep(3 * 1000);
	}

	if (SUCCESS != rc) {
		IOT_ERROR("An error occurred in the loop %d", rc);
	}

	IOT_INFO("Disconnecting");
	rc = aws_iot_shadow_disconnect_ptr(&mqttClient);

	if (SUCCESS != rc) {
		IOT_ERROR("Disconnect error %d", rc);
	}

	FreeLibrary(hModule);

	return 0;
}

static void shadowUpdateStatusCallback(const char *pThingName, ShadowActions_t action, Shadow_Ack_Status_t status, const char *pReceivedJsonDocument, void *pContextData) {
	IOT_UNUSED(pThingName);
	IOT_UNUSED(action);
	IOT_UNUSED(pReceivedJsonDocument);
	IOT_UNUSED(pContextData);

	if (SHADOW_ACK_TIMEOUT == status) {
		IOT_INFO("Update Timeout--");
	}
	else if (SHADOW_ACK_REJECTED == status) {
		IOT_INFO("Update RejectedXX");
	}
	else if (SHADOW_ACK_ACCEPTED == status) {
		IOT_INFO("Update Accepted !!");
	}
}

static void simulateRoomTemperature(float *pRoomTemperature) {
	static float deltaChange;

	if (*pRoomTemperature >= ROOMTEMPERATURE_UPPERLIMIT) {
		deltaChange = -0.5f;
	}
	else if (*pRoomTemperature <= ROOMTEMPERATURE_LOWERLIMIT) {
		deltaChange = 0.5f;
	}

	*pRoomTemperature += deltaChange;
}

static void windowActuate_Callback(const char *pJsonString, uint32_t JsonStringDataLen, jsonStruct_t *pContext) {
	IOT_UNUSED(pJsonString);
	IOT_UNUSED(JsonStringDataLen);

	if (pContext != NULL) {
		IOT_INFO("Delta - Window state changed to %d", *(bool *)(pContext->pData));
	}
}
