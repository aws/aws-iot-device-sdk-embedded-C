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

#include "aws_iot_mqtt_interface.h"
#include "MQTTClient.h"
#include "aws_iot_config.h"

static Network n;
static Client c;
static iot_disconnect_handler clientDisconnectHandler;

static unsigned char writebuf[AWS_IOT_MQTT_TX_BUF_LEN];
static unsigned char readbuf[AWS_IOT_MQTT_RX_BUF_LEN];



const MQTTConnectParams MQTTConnectParamsDefault = {
		.pHostURL = AWS_IOT_MQTT_HOST,
		.port = AWS_IOT_MQTT_PORT,
		.pRootCALocation = NULL,
		.pDeviceCertLocation = NULL,
		.pDevicePrivateKeyLocation = NULL,
		.pClientID = NULL,
		.pUserName = NULL,
		.pPassword = NULL,
		.MQTTVersion = MQTT_3_1_1,
		.KeepAliveInterval_sec = 10,
		.isCleansession = true,
		.isWillMsgPresent = false,
		.will={.pTopicName = NULL, .pMessage = NULL, .isRetained = false, .qos = QOS_0},
		.mqttCommandTimeout_ms = 1000,
		.tlsHandshakeTimeout_ms = 2000,
		.isSSLHostnameVerify = true,
		.disconnectHandler = NULL
};

const MQTTPublishParams MQTTPublishParamsDefault={
		.pTopic = NULL,
		.MessageParams = {.qos = QOS_0, .isRetained=false, .isDuplicate = false, .id = 0, .pPayload = NULL, .PayloadLen = 0}
};
const MQTTSubscribeParams MQTTSubscribeParamsDefault={
		.pTopic = NULL,
		.qos = QOS_0,
		.mHandler = NULL
};
const MQTTCallbackParams MQTTCallbackParamsDefault={
		.pTopicName = NULL,
		.TopicNameLen = 0,
		.MessageParams = {.qos = QOS_0, .isRetained=false, .isDuplicate = false, .id = 0, .pPayload = NULL, .PayloadLen = 0}
};
const MQTTMessageParams MQTTMessageParamsDefault={
		.qos = QOS_0,
		.isRetained=false,
		.isDuplicate = false,
		.id = 0,
		.pPayload = NULL,
		.PayloadLen = 0
};
const MQTTwillOptions MQTTwillOptionsDefault={
		.pTopicName = NULL,
		.pMessage = NULL,
		.isRetained = false,
		.qos = QOS_0
};

#define GETLOWER4BYTES 0x0FFFFFFFF
void pahoMessageCallback(MessageData* md) {
	MQTTMessage* message = md->message;
	MQTTCallbackParams params;

	// early exit if we do not have a valid callback pointer
	if (md->applicationHandler == NULL) {
		return;
	}

	if (NULL != md->topicName->lenstring.data) {
		params.pTopicName = md->topicName->lenstring.data;
		params.TopicNameLen = (uint16_t)(md->topicName->lenstring.len);
	}
	if (NULL != message) {
		params.MessageParams.PayloadLen = message->payloadlen & GETLOWER4BYTES;
		params.MessageParams.pPayload = (char*) message->payload;
		params.MessageParams.isDuplicate = message->dup;
		params.MessageParams.qos = (QoSLevel)message->qos;
		params.MessageParams.isRetained = message->retained;
		params.MessageParams.id = message->id;
	}

	((iot_message_handler)(md->applicationHandler))(params);
}

void pahoDisconnectHandler(void) {
	if (clientDisconnectHandler != NULL) {
		clientDisconnectHandler();
	}
}

static IoT_Error_t parseConnectParamsForError(MQTTConnectParams *pParams) {
	IoT_Error_t rc = NONE_ERROR;
	if (
	NULL == pParams->pClientID ||
	NULL == pParams->pHostURL) {
		rc = NULL_VALUE_ERROR;
	}
	return rc;
}

static bool isPowerCycle = true;

IoT_Error_t aws_iot_mqtt_connect(MQTTConnectParams *pParams) {
	IoT_Error_t rc = NONE_ERROR;

	rc = parseConnectParamsForError(pParams);

	if (NONE_ERROR == rc) {

		iot_tls_init(&n);
		TLSConnectParams TLSParams;
		TLSParams.DestinationPort = pParams->port;
		TLSParams.pDestinationURL = pParams->pHostURL;
		TLSParams.pDeviceCertLocation = pParams->pDeviceCertLocation;
		TLSParams.pDevicePrivateKeyLocation = pParams->pDevicePrivateKeyLocation;
		TLSParams.pRootCALocation = pParams->pRootCALocation;
		TLSParams.timeout_ms = pParams->tlsHandshakeTimeout_ms;
		TLSParams.ServerVerificationFlag = pParams->isSSLHostnameVerify;

		rc = iot_tls_connect(&n, TLSParams);

		if (NONE_ERROR == rc) {
			// This implementation assumes you are not going to switch between cleansession 1 to 0
			// As we don't have a default subscription handler support in the MQTT client every time a device power cycles it has to re-subscribe to let the MQTT client to pass the message up to the application callback.
			// The default message handler will be implemented in the future revisions.
			if(pParams->isCleansession || isPowerCycle){
				MQTTClient(&c, &n, (unsigned int)(pParams->mqttCommandTimeout_ms), writebuf, AWS_IOT_MQTT_TX_BUF_LEN, readbuf, AWS_IOT_MQTT_RX_BUF_LEN);
				isPowerCycle = false;
			}

			MQTTPacket_connectData data = MQTTPacket_connectData_initializer;

			data.willFlag = pParams->isWillMsgPresent;
			// compatible type for MQTT_Ver_t
			switch (pParams->MQTTVersion) {
			case MQTT_3_1:
				data.MQTTVersion = (unsigned char) (3);
				break;
			case MQTT_3_1_1:
				data.MQTTVersion = (unsigned char) (4);
				break;
			default:
				data.MQTTVersion = (unsigned char) (4); // default MQTT version = 3.1.1
			}

			// register our disconnect handler, save customer's handler
			setDisconnectHandler(&c, pahoDisconnectHandler);
			clientDisconnectHandler = pParams->disconnectHandler;

			data.clientID.cstring = pParams->pClientID;
			data.username.cstring = pParams->pUserName;
			data.password.cstring = pParams->pPassword;
			data.will.topicName.cstring = (char*)pParams->will.pTopicName;
			data.will.message.cstring = (char*)pParams->will.pMessage;
			data.will.qos = pParams->will.qos;
			data.will.retained = pParams->will.isRetained;
			data.keepAliveInterval = pParams->KeepAliveInterval_sec;
			data.cleansession = pParams->isCleansession;
			if (0 != MQTTConnect(&c, &data)) {
				rc = CONNECTION_ERROR;
			}
		}
	}

	return rc;
}

IoT_Error_t aws_iot_mqtt_subscribe(MQTTSubscribeParams *pParams) {
	IoT_Error_t rc = NONE_ERROR;

	if (0 != MQTTSubscribe(&c, pParams->pTopic, (enum QoS)pParams->qos, pahoMessageCallback, (void (*)(void))(pParams->mHandler))) {
			rc = SUBSCRIBE_ERROR;
	}
	return rc;
}

IoT_Error_t aws_iot_mqtt_publish(MQTTPublishParams *pParams) {
	IoT_Error_t rc = NONE_ERROR;

	MQTTMessage Message;
	Message.dup = pParams->MessageParams.isDuplicate;
	Message.id = pParams->MessageParams.id;
	Message.payload = pParams->MessageParams.pPayload;
	Message.payloadlen = pParams->MessageParams.PayloadLen;
	Message.qos = (enum QoS)pParams->MessageParams.qos;
	Message.retained = pParams->MessageParams.isRetained;

	if(0 != MQTTPublish(&c, pParams->pTopic, &Message)){
		rc = PUBLISH_ERROR;
	}

	return rc;
}

IoT_Error_t aws_iot_mqtt_unsubscribe(char *pTopic) {
	IoT_Error_t rc = NONE_ERROR;

	if(0 != MQTTUnsubscribe(&c, pTopic)){
		rc = UNSUBSCRIBE_ERROR;
	}
	return rc;
}

IoT_Error_t aws_iot_mqtt_disconnect() {
	IoT_Error_t rc = NONE_ERROR;

	if(0 != MQTTDisconnect(&c)){
		rc = DISCONNECT_ERROR;
	}
	iot_tls_disconnect(&n);
	return rc;
}

IoT_Error_t aws_iot_mqtt_yield(int timeout) {
	IoT_Error_t rc = NONE_ERROR;
	if(0 != MQTTYield(&c, timeout)){
		rc = YIELD_ERROR;
	}
	return rc;
}

bool aws_iot_is_mqtt_connected(void) {
	return c.isconnected;
}

void aws_iot_mqtt_init(MQTTClient_t *pClient){
	pClient->connect = aws_iot_mqtt_connect;
	pClient->disconnect = aws_iot_mqtt_disconnect;
	pClient->isConnected = aws_iot_is_mqtt_connected;
	pClient->publish = aws_iot_mqtt_publish;
	pClient->subscribe = aws_iot_mqtt_subscribe;
	pClient->unsubscribe = aws_iot_mqtt_unsubscribe;
	pClient->yield = aws_iot_mqtt_yield;
}
