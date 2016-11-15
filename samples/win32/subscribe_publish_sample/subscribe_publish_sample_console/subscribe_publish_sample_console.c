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

/*
*  Function prototypes
*/
static void iot_subscribe_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen, IoT_Publish_Message_Params *params, void *pData);
static void disconnectCallbackHandler(AWS_IoT_Client *pClient, void *data);

static AWS_IOT_MQTT_INIT aws_iot_mqtt_init_ptr = NULL;
static AWS_IOT_MQTT_CONNECT aws_iot_mqtt_connect_ptr = NULL;
static AWS_IOT_MQTT_PUBLISH aws_iot_mqtt_publish_ptr = NULL;
static AWS_IOT_MQTT_SUBSCRIBE aws_iot_mqtt_subscribe_ptr = NULL;
static AWS_IOT_MQTT_RESUBSCRIBE aws_iot_mqtt_resubscribe_ptr = NULL;
static AWS_IOT_MQTT_UNSUBSCRIBE aws_iot_mqtt_unsubscribe_ptr = NULL;
static AWS_IOT_MQTT_DISCONNECT aws_iot_mqtt_disconnect_ptr = NULL;
static AWS_IOT_MQTT_YIELD aws_iot_mqtt_yield_ptr = NULL;
static AWS_IOT_MQTT_ATTEMPT_RECONNECT aws_iot_mqtt_attempt_reconnect_ptr = NULL;
static AWS_IOT_MQTT_AUTORECONNECT_ENABLED aws_iot_is_autoreconnect_enabled_ptr = NULL;
static AWS_IOT_MQTT_AUTORECONNECT_SET_STATUS aws_iot_mqtt_autoreconnect_set_status_ptr = NULL;

enum { PATH_MAX = 512 };

static char certDirectory[PATH_MAX + 1] = "..\\..\\..\\..\\certs";
static char HostAddress[255] = AWS_IOT_MQTT_HOST;
static uint32_t port = AWS_IOT_MQTT_PORT;
static uint8_t numPubs = 5;

int main()
{
	IoT_Error_t rc = FAILURE;
	int32_t i = 0;

	AWS_IoT_Client client;
	IoT_Client_Init_Params mqttInitParams = iotClientInitParamsDefault;
	IoT_Client_Connect_Params connectParams = iotClientConnectParamsDefault;

	IoT_Publish_Message_Params paramsQOS0;
	IoT_Publish_Message_Params paramsQOS1;

	uint32_t publishCount = 2;
	bool infinitePublishFlag = true;

	char rootCA[PATH_MAX + 1];
	char clientCRT[PATH_MAX + 1];
	char clientKey[PATH_MAX + 1];
	char CurrentWD[PATH_MAX + 1];
	char cPayload[100];

	IOT_INFO("\nAWS IoT SDK Version %d.%d.%d-%s\n", VERSION_MAJOR, VERSION_MINOR, VERSION_PATCH, VERSION_TAG);

	GetCurrentDirectoryA(sizeof(CurrentWD), CurrentWD);
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

	HMODULE hModule = LoadLibraryA("aws-iot-sdk.dll");

	aws_iot_mqtt_init_ptr = (AWS_IOT_MQTT_INIT)GetProcAddress(hModule, "aws_iot_mqtt_init");
	aws_iot_mqtt_connect_ptr = (AWS_IOT_MQTT_CONNECT)GetProcAddress(hModule, "aws_iot_mqtt_connect");
	aws_iot_mqtt_publish_ptr = (AWS_IOT_MQTT_PUBLISH)GetProcAddress(hModule, "aws_iot_mqtt_publish");
	aws_iot_mqtt_subscribe_ptr = (AWS_IOT_MQTT_SUBSCRIBE)GetProcAddress(hModule, "aws_iot_mqtt_subscribe");
	aws_iot_mqtt_resubscribe_ptr = (AWS_IOT_MQTT_RESUBSCRIBE)GetProcAddress(hModule, "aws_iot_mqtt_resubscribe");
	aws_iot_mqtt_unsubscribe_ptr = (AWS_IOT_MQTT_UNSUBSCRIBE)GetProcAddress(hModule, "aws_iot_mqtt_unsubscribe");
	aws_iot_mqtt_disconnect_ptr = (AWS_IOT_MQTT_DISCONNECT)GetProcAddress(hModule, "aws_iot_mqtt_disconnect");
	aws_iot_mqtt_yield_ptr = (AWS_IOT_MQTT_YIELD)GetProcAddress(hModule, "aws_iot_mqtt_yield");
	aws_iot_mqtt_attempt_reconnect_ptr = (AWS_IOT_MQTT_ATTEMPT_RECONNECT)GetProcAddress(hModule, "aws_iot_mqtt_attempt_reconnect");
	aws_iot_is_autoreconnect_enabled_ptr = (AWS_IOT_MQTT_AUTORECONNECT_ENABLED)GetProcAddress(hModule, "aws_iot_is_autoreconnect_enabled");
	aws_iot_mqtt_autoreconnect_set_status_ptr = (AWS_IOT_MQTT_AUTORECONNECT_SET_STATUS)GetProcAddress(hModule, "aws_iot_mqtt_autoreconnect_set_status");

	rc = aws_iot_mqtt_init_ptr(&client, &mqttInitParams);
	if (SUCCESS != rc) 
	{
		IOT_ERROR("aws_iot_mqtt_init returned error : %d ", rc);
		return rc;
	}

	connectParams.keepAliveIntervalInSec = 10;
	connectParams.isCleanSession = true;
	connectParams.MQTTVersion = MQTT_3_1_1;
	connectParams.pClientID = AWS_IOT_MQTT_CLIENT_ID;
	connectParams.clientIDLen = (uint16_t)strlen(AWS_IOT_MQTT_CLIENT_ID);
	connectParams.isWillMsgPresent = false;

	IOT_INFO("Connecting...");
	rc = aws_iot_mqtt_connect_ptr(&client, &connectParams);
	if (SUCCESS != rc) 
	{
		IOT_ERROR("Error(%d) connecting to %s:%d", rc, mqttInitParams.pHostURL, mqttInitParams.port);
		return rc;
	}

	/*
	* Enable Auto Reconnect functionality. Minimum and Maximum time of Exponential backoff are set in aws_iot_config.h
	*  #AWS_IOT_MQTT_MIN_RECONNECT_WAIT_INTERVAL
	*  #AWS_IOT_MQTT_MAX_RECONNECT_WAIT_INTERVAL
	*/
	rc = aws_iot_mqtt_autoreconnect_set_status_ptr(&client, true);
	if (SUCCESS != rc) 
	{
		IOT_ERROR("Unable to set Auto Reconnect to true - %d", rc);
		return rc;
	}

	//IOT_INFO("Subscribing...");
	//rc = aws_iot_mqtt_subscribe_ptr(&client, "AVR-CAN", 11, QOS0, iot_subscribe_callback_handler, NULL);
	//if (SUCCESS != rc) {
	//	IOT_ERROR("Error subscribing : %d ", rc);
	//	return rc;
	//}

	sprintf_s(cPayload, 100, "%s : %d ", "Hello from Win32 subscribe_publish_sample", i);

	paramsQOS0.qos = QOS0;
	paramsQOS0.payload = (void *)cPayload;
	paramsQOS0.isRetained = 0;

	paramsQOS1.qos = QOS1;
	paramsQOS1.payload = (void *)cPayload;
	paramsQOS1.isRetained = 0;

	if (publishCount != 0) 
	{
		infinitePublishFlag = false;
	}

	while ((NETWORK_ATTEMPTING_RECONNECT == rc || NETWORK_RECONNECTED == rc || SUCCESS == rc)
		&& (publishCount > 0 || infinitePublishFlag)) 
	{
		//Max time the yield function will wait for read messages
		rc = aws_iot_mqtt_yield_ptr(&client, 100);
		if (NETWORK_ATTEMPTING_RECONNECT == rc) 
		{
			// If the client is attempting to reconnect we will skip the rest of the loop.
			continue;
		}

		IOT_INFO("-->sleep");
		Sleep(1);
		sprintf_s(cPayload, 100, "%s : %d ", "Hello from Win32 subscribe_publish_sample QOS0", i++);
		IOT_INFO(cPayload);
		paramsQOS0.payloadLen = strlen(cPayload);
		rc = aws_iot_mqtt_publish_ptr(&client, "WIN32_SUB_PUB", 11, &paramsQOS0);
		if (publishCount > 0) 
		{
			publishCount--;
		}

		sprintf_s(cPayload, 100, "%s : %d ", "Hello from Win32 subscribe_publish_sample QOS1", i++);
		paramsQOS1.payloadLen = strlen(cPayload);
		rc = aws_iot_mqtt_publish_ptr(&client, "WIN32_SUB-_PUB", 11, &paramsQOS1);
		if (rc == MQTT_REQUEST_TIMEOUT_ERROR) 
		{
			IOT_WARN("QOS1 publish ack not received.\n");
			rc = SUCCESS;
		}
		if (publishCount > 0) 
		{
			publishCount--;
		}
	}

	if (SUCCESS != rc) 
	{
		IOT_ERROR("An error occurred in the loop.\n");
	}
	else {
		IOT_INFO("Publish done\n");
	}

	FreeLibrary(hModule);

	return 0;
}

void iot_subscribe_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
	IoT_Publish_Message_Params *params, void *pData) 
{
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	IOT_INFO("Subscribe callback");
	IOT_INFO("%.*s\t%.*s", topicNameLen, topicName, (int)params->payloadLen, (char*)params->payload);
}

void disconnectCallbackHandler(AWS_IoT_Client *pClient, void *data) 
{
	IOT_WARN("MQTT Disconnect");
	IoT_Error_t rc = FAILURE;

	if (NULL == pClient)
	{
		return;
	}

	IOT_UNUSED(data);

	if (aws_iot_is_autoreconnect_enabled_ptr(pClient))
	{
		IOT_INFO("Auto Reconnect is enabled, Reconnecting attempt will start now");
	}
	else
	{
		IOT_WARN("Auto Reconnect not enabled. Starting manual reconnect...");
		rc = aws_iot_mqtt_attempt_reconnect_ptr(pClient);
		if (NETWORK_RECONNECTED == rc)
		{
			IOT_WARN("Manual Reconnect Successful");
		}
		else
		{
			IOT_WARN("Manual Reconnect Failed - %d", rc);
		}
	}
}

