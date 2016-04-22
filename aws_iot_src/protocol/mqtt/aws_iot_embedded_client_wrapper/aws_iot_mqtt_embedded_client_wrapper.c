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

#include "timer_interface.h"
#include "aws_iot_mqtt_interface.h"
#include "MQTTClient.h"
#include "aws_iot_config.h"

static Client c;

static iot_disconnect_handler clientDisconnectHandler;

static unsigned char writebuf[AWS_IOT_MQTT_TX_BUF_LEN];
static unsigned char readbuf[AWS_IOT_MQTT_RX_BUF_LEN];

const MQTTConnectParams MQTTConnectParamsDefault = {
		.enableAutoReconnect = 0,
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
	if(NULL != clientDisconnectHandler) {
		clientDisconnectHandler();
	}
}

static bool isPowerCycle = true;

IoT_Error_t aws_iot_mqtt_connect(MQTTConnectParams *pParams) {
	IoT_Error_t rc = NONE_ERROR;
	MQTTReturnCode pahoRc = SUCCESS;

	if(NULL == pParams || NULL == pParams->pClientID || NULL == pParams->pHostURL) {
		return NULL_VALUE_ERROR;
	}

	TLSConnectParams TLSParams;
	TLSParams.DestinationPort = pParams->port;
	TLSParams.pDestinationURL = pParams->pHostURL;
	TLSParams.pDeviceCertLocation = pParams->pDeviceCertLocation;
	TLSParams.pDevicePrivateKeyLocation = pParams->pDevicePrivateKeyLocation;
	TLSParams.pRootCALocation = pParams->pRootCALocation;
	TLSParams.timeout_ms = pParams->tlsHandshakeTimeout_ms;
	TLSParams.ServerVerificationFlag = pParams->isSSLHostnameVerify;

	// This implementation assumes you are not going to switch between cleansession 1 to 0
	// As we don't have a default subscription handler support in the MQTT client every time a device power cycles it has to re-subscribe to let the MQTT client to pass the message up to the application callback.
	// The default message handler will be implemented in the future revisions.
	if(pParams->isCleansession || isPowerCycle){
		pahoRc = MQTTClient(&c, (unsigned int)(pParams->mqttCommandTimeout_ms), writebuf,
				   AWS_IOT_MQTT_TX_BUF_LEN, readbuf, AWS_IOT_MQTT_RX_BUF_LEN,
				   pParams->enableAutoReconnect, iot_tls_init, &TLSParams);
		if(SUCCESS != pahoRc) {
			return CONNECTION_ERROR;
		}
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
	data.will.qos = (enum QoS)pParams->will.qos;
	data.will.retained = pParams->will.isRetained;
	data.keepAliveInterval = pParams->KeepAliveInterval_sec;
	data.cleansession = pParams->isCleansession;

	pahoRc = MQTTConnect(&c, &data);
	if(MQTT_NETWORK_ALREADY_CONNECTED_ERROR == pahoRc) {
		rc = NETWORK_ALREADY_CONNECTED;
	} else if(SUCCESS != pahoRc) {
		rc = CONNECTION_ERROR;
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

	return rc;
}

IoT_Error_t aws_iot_mqtt_yield(int timeout) {
	MQTTReturnCode pahoRc = MQTTYield(&c, timeout);
	IoT_Error_t rc = NONE_ERROR;
	if(MQTT_NETWORK_RECONNECTED == pahoRc){
		rc = RECONNECT_SUCCESSFUL;
	} else if(SUCCESS == pahoRc){
		rc = NONE_ERROR;
	} else if(MQTT_NULL_VALUE_ERROR == pahoRc) {
		rc = NULL_VALUE_ERROR;
	} else if(MQTT_NETWORK_DISCONNECTED_ERROR == pahoRc) {
		rc = NETWORK_DISCONNECTED;
	} else if(MQTT_RECONNECT_TIMED_OUT == pahoRc) {
		rc = NETWORK_RECONNECT_TIMED_OUT;
	} else if(MQTT_ATTEMPTING_RECONNECT == pahoRc) {
		rc = NETWORK_ATTEMPTING_RECONNECT;
	} else if(MQTT_BUFFER_RX_MESSAGE_INVALID == pahoRc){
		rc = RX_MESSAGE_INVALID;
	} else if(MQTTPACKET_BUFFER_TOO_SHORT == pahoRc){
		rc = RX_MESSAGE_BIGGER_THAN_MQTT_RX_BUF;
	} else {
		rc = YIELD_ERROR;
	}

	return rc;
}

IoT_Error_t aws_iot_mqtt_attempt_reconnect() {
	MQTTReturnCode pahoRc = MQTTAttemptReconnect(&c);
	IoT_Error_t rc = RECONNECT_SUCCESSFUL;
	if(MQTT_NETWORK_RECONNECTED == pahoRc){
		rc = RECONNECT_SUCCESSFUL;
	} else if(MQTT_NULL_VALUE_ERROR == pahoRc) {
		rc = NULL_VALUE_ERROR;
	} else if(MQTT_NETWORK_DISCONNECTED_ERROR == pahoRc) {
		rc = NETWORK_DISCONNECTED;
	} else if(MQTT_RECONNECT_TIMED_OUT == pahoRc) {
		rc = NETWORK_RECONNECT_TIMED_OUT;
	} else if(MQTT_NETWORK_ALREADY_CONNECTED_ERROR == pahoRc) {
		rc = NETWORK_ALREADY_CONNECTED;
	} else {
		rc = GENERIC_ERROR;
	}

	return rc;
}

IoT_Error_t aws_iot_mqtt_autoreconnect_set_status(bool value) {
	MQTTReturnCode rc = setAutoReconnectEnabled(&c, (uint8_t) value);

	if(MQTT_NULL_VALUE_ERROR == rc) {
		return NULL_VALUE_ERROR;
	}

	return NONE_ERROR;
}

bool aws_iot_is_mqtt_connected(void) {
	return MQTTIsConnected(&c);
}

bool aws_iot_is_autoreconnect_enabled(void) {
	return MQTTIsAutoReconnectEnabled(&c);
}

void aws_iot_mqtt_init(MQTTClient_t *pClient){
	pClient->connect = aws_iot_mqtt_connect;
	pClient->disconnect = aws_iot_mqtt_disconnect;
	pClient->isConnected = aws_iot_is_mqtt_connected;
	pClient->reconnect = aws_iot_mqtt_attempt_reconnect;
	pClient->publish = aws_iot_mqtt_publish;
	pClient->subscribe = aws_iot_mqtt_subscribe;
	pClient->unsubscribe = aws_iot_mqtt_unsubscribe;
	pClient->yield = aws_iot_mqtt_yield;
	pClient->isAutoReconnectEnabled = aws_iot_is_autoreconnect_enabled;
	pClient->setAutoReconnectStatus = aws_iot_mqtt_autoreconnect_set_status;
}
