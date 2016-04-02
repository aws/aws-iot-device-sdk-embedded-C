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

#include "aws_iot_error.h"
#include "aws_iot_log.h"
#include "aws_iot_shadow_actions.h"
#include "aws_iot_shadow_json.h"
#include "aws_iot_shadow_key.h"
#include "aws_iot_shadow_records.h"

const ShadowParameters_t ShadowParametersDefault = {
		.pMyThingName = AWS_IOT_MY_THING_NAME,
		.pMqttClientId = AWS_IOT_MQTT_CLIENT_ID,
		.pHost = AWS_IOT_MQTT_HOST,
		.port = AWS_IOT_MQTT_PORT,
		.pRootCA = NULL,
		.pClientCRT = NULL,
		.pClientKey = NULL
};

void aws_iot_shadow_reset_last_received_version(void) {
	shadowJsonVersionNum = 0;
}

uint32_t aws_iot_shadow_get_last_received_version(void) {
	return shadowJsonVersionNum;
}

void aws_iot_shadow_enable_discard_old_delta_msgs(void) {
	shadowDiscardOldDeltaFlag = true;
}

void aws_iot_shadow_disable_discard_old_delta_msgs(void) {
	shadowDiscardOldDeltaFlag = false;
}

IoT_Error_t aws_iot_shadow_init(MQTTClient_t *pClient) {

	IoT_Error_t rc = NONE_ERROR;

	if (pClient == NULL) {
		return NULL_VALUE_ERROR;
	}

	resetClientTokenSequenceNum();
	aws_iot_shadow_reset_last_received_version();
	initDeltaTokens();
	return NONE_ERROR;
}

IoT_Error_t aws_iot_shadow_connect(MQTTClient_t *pClient, ShadowParameters_t *pParams) {
	IoT_Error_t rc = NONE_ERROR;
	MQTTConnectParams ConnectParams = MQTTConnectParamsDefault;
	if (pClient == NULL) {
		return NULL_VALUE_ERROR;
	}

	if (pClient->connect == NULL) {
		return NULL_VALUE_ERROR;
	}

	snprintf(myThingName, MAX_SIZE_OF_THING_NAME, "%s", pParams->pMyThingName );
	snprintf(mqttClientID, MAX_SIZE_OF_UNIQUE_CLIENT_ID_BYTES, "%s", pParams->pMqttClientId );

	DEBUG("Thing Name %s", myThingName);
	DEBUG("MQTT Client ID %s", mqttClientID);

	ConnectParams.KeepAliveInterval_sec = 10;
	ConnectParams.MQTTVersion = MQTT_3_1_1;
	ConnectParams.mqttCommandTimeout_ms = 2000;
	ConnectParams.tlsHandshakeTimeout_ms = 10000;
	ConnectParams.isCleansession = true;
	ConnectParams.isSSLHostnameVerify = true;
	ConnectParams.isWillMsgPresent = false;
	ConnectParams.pClientID = pParams->pMqttClientId;
	ConnectParams.pDeviceCertLocation = pParams->pClientCRT;
	ConnectParams.pDevicePrivateKeyLocation = pParams->pClientKey;
	ConnectParams.pRootCALocation = pParams->pRootCA;
	ConnectParams.pPassword = NULL;
	ConnectParams.pUserName = NULL;
	ConnectParams.pHostURL = pParams->pHost;
	ConnectParams.port = pParams->port;
	ConnectParams.disconnectHandler = NULL;

	rc = pClient->connect(&ConnectParams);

	if(rc == NONE_ERROR){
		initializeRecords(pClient);
	}

	return rc;
}

IoT_Error_t aws_iot_shadow_register_delta(MQTTClient_t *pClient, jsonStruct_t *pStruct) {
	IoT_Error_t rc = NONE_ERROR;

	if (!(pClient->isConnected())) {
		return CONNECTION_ERROR;
	}

	rc = registerJsonTokenOnDelta(pStruct);

	return rc;
}

IoT_Error_t aws_iot_shadow_yield(MQTTClient_t *pClient, int timeout) {
	HandleExpiredResponseCallbacks();
	return pClient->yield(timeout);
}

IoT_Error_t aws_iot_shadow_disconnect(MQTTClient_t *pClient) {
	return pClient->disconnect();
}

IoT_Error_t aws_iot_shadow_update(MQTTClient_t *pClient, const char *pThingName, char *pJsonString,
		fpActionCallback_t callback, void *pContextData, uint8_t timeout_seconds, bool isPersistentSubscribe) {

	IoT_Error_t ret_val = NONE_ERROR;

	if (!(pClient->isConnected())) {
		return CONNECTION_ERROR;
	}

	ret_val = iot_shadow_action(pClient, pThingName, SHADOW_UPDATE, pJsonString, callback, pContextData,
			timeout_seconds, isPersistentSubscribe);

	return ret_val;
}

IoT_Error_t aws_iot_shadow_delete(MQTTClient_t *pClient, const char *pThingName, fpActionCallback_t callback,
		void *pContextData, uint8_t timeout_seconds, bool isPersistentSubscribe) {
	IoT_Error_t ret_val = NONE_ERROR;

	if (!(pClient->isConnected())) {
		return CONNECTION_ERROR;
	}

	char deleteRequestJsonBuf[MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE];
	iot_shadow_delete_request_json(deleteRequestJsonBuf);
	ret_val = iot_shadow_action(pClient, pThingName, SHADOW_DELETE, deleteRequestJsonBuf, callback, pContextData,
			timeout_seconds, isPersistentSubscribe);

	return ret_val;
}

IoT_Error_t aws_iot_shadow_get(MQTTClient_t *pClient, const char *pThingName, fpActionCallback_t callback,
		void *pContextData, uint8_t timeout_seconds, bool isPersistentSubscribe) {

	IoT_Error_t ret_val = NONE_ERROR;

	if (!(pClient->isConnected())) {
		return CONNECTION_ERROR;
	}

	char getRequestJsonBuf[MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE];

	iot_shadow_get_request_json(getRequestJsonBuf);

	ret_val = iot_shadow_action(pClient, pThingName, SHADOW_GET, getRequestJsonBuf, callback, pContextData,
			timeout_seconds, isPersistentSubscribe);

	return ret_val;
}
