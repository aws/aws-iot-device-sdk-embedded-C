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

#include "aws_iot_shadow_records.h"

#include <string.h>
#include <stdio.h>

#include "timer_interface.h"
#include "aws_iot_json_utils.h"
#include "aws_iot_log.h"
#include "aws_iot_shadow_json.h"
#include "aws_iot_config.h"

typedef struct {
	char clientTokenID[MAX_SIZE_CLIENT_ID_WITH_SEQUENCE];
	char thingName[MAX_SIZE_OF_THING_NAME];
	ShadowActions_t action;
	fpActionCallback_t callback;
	void *pCallbackContext;
	bool isFree;
	Timer timer;
} ToBeReceivedAckRecord_t;

typedef struct {
	const char *pKey;
	void *pStruct;
	jsonStructCallback_t callback;
	bool isFree;
} JsonTokenTable_t;

typedef struct {
	char Topic[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	uint8_t count;
	bool isFree;
	bool isSticky;
} SubscriptionRecord_t;

typedef enum {
	SHADOW_ACCEPTED, SHADOW_REJECTED, SHADOW_ACTION
} ShadowAckTopicTypes_t;

ToBeReceivedAckRecord_t AckWaitList[MAX_ACKS_TO_COMEIN_AT_ANY_GIVEN_TIME];

MQTTClient_t *pMqttClient;

char myThingName[MAX_SIZE_OF_THING_NAME];
char mqttClientID[MAX_SIZE_OF_UNIQUE_CLIENT_ID_BYTES];

char shadowDeltaTopic[MAX_SHADOW_TOPIC_LENGTH_BYTES];

#define MAX_TOPICS_AT_ANY_GIVEN_TIME 2*MAX_THINGNAME_HANDLED_AT_ANY_GIVEN_TIME
SubscriptionRecord_t SubscriptionList[MAX_TOPICS_AT_ANY_GIVEN_TIME];

#define SUBSCRIBE_SETTLING_TIME 2
char shadowRxBuf[SHADOW_MAX_SIZE_OF_RX_BUFFER];

static JsonTokenTable_t tokenTable[MAX_JSON_TOKEN_EXPECTED];
static uint32_t tokenTableIndex = 0;
static bool deltaTopicSubscribedFlag = false;
uint32_t shadowJsonVersionNum = 0;
bool shadowDiscardOldDeltaFlag = true;

// local helper functions
static int AckStatusCallback(MQTTCallbackParams params);
static int shadow_delta_callback(MQTTCallbackParams params);
static void topicNameFromThingAndAction(char *pTopic, const char *pThingName, ShadowActions_t action,
		ShadowAckTopicTypes_t ackType);
static int16_t getNextFreeIndexOfSubscriptionList(void);
static void unsubscribeFromAcceptedAndRejected(uint8_t index);

void initDeltaTokens(void) {
	uint32_t i;
	for (i = 0; i < MAX_JSON_TOKEN_EXPECTED; i++) {
		tokenTable[i].isFree = true;
	}
	tokenTableIndex = 0;
	deltaTopicSubscribedFlag = false;
}

IoT_Error_t registerJsonTokenOnDelta(jsonStruct_t *pStruct) {

	IoT_Error_t rc = NONE_ERROR;

	if (!deltaTopicSubscribedFlag) {
		MQTTSubscribeParams subParams;
		subParams.mHandler = shadow_delta_callback;
		snprintf(shadowDeltaTopic,MAX_SHADOW_TOPIC_LENGTH_BYTES, "$aws/things/%s/shadow/update/delta", myThingName);
		subParams.pTopic = shadowDeltaTopic;
		subParams.qos = QOS_0;
		rc = pMqttClient->subscribe(&subParams);
		DEBUG("delta topic %s", shadowDeltaTopic);
		deltaTopicSubscribedFlag = true;
	}

	if (tokenTableIndex >= MAX_JSON_TOKEN_EXPECTED) {
		return GENERIC_ERROR;
	}

	tokenTable[tokenTableIndex].pKey = pStruct->pKey;
	tokenTable[tokenTableIndex].callback = pStruct->cb;
	tokenTable[tokenTableIndex].pStruct = pStruct;
	tokenTable[tokenTableIndex].isFree = false;
	tokenTableIndex++;

	return rc;
}

static int16_t getNextFreeIndexOfSubscriptionList(void) {
	uint8_t i;
	for (i = 0; i < MAX_TOPICS_AT_ANY_GIVEN_TIME; i++) {
		if (SubscriptionList[i].isFree) {
			SubscriptionList[i].isFree = false;
			return i;
		}
	}
	return -1;
}

static void topicNameFromThingAndAction(char *pTopic, const char *pThingName, ShadowActions_t action,
		ShadowAckTopicTypes_t ackType) {

	char actionBuf[10];
	char ackTypeBuf[10];

	if (action == SHADOW_GET) {
		strcpy(actionBuf, "get");
	} else if (action == SHADOW_UPDATE) {
		strcpy(actionBuf, "update");
	} else if (action == SHADOW_DELETE) {
		strcpy(actionBuf, "delete");
	}

	if (ackType == SHADOW_ACCEPTED) {
		strcpy(ackTypeBuf, "accepted");
	} else if (ackType == SHADOW_REJECTED) {
		strcpy(ackTypeBuf, "rejected");
	}

	if (ackType == SHADOW_ACTION) {
		sprintf(pTopic, "$aws/things/%s/shadow/%s", pThingName, actionBuf);
	} else {
		sprintf(pTopic, "$aws/things/%s/shadow/%s/%s", pThingName, actionBuf, ackTypeBuf);
	}
}

static bool isAckForMyThingName(const char *pTopicName) {
	if (strstr(pTopicName, myThingName) != NULL && ((strstr(pTopicName, "get/accepted") != NULL) || (strstr(pTopicName, "delta") != NULL))) {
		return true;
	}
	return false;
}

static int AckStatusCallback(MQTTCallbackParams params) {
	int32_t tokenCount;
	int32_t i;
	void *pJsonHandler;
	char temporaryClientToken[MAX_SIZE_CLIENT_ID_WITH_SEQUENCE];

	if (params.MessageParams.PayloadLen > SHADOW_MAX_SIZE_OF_RX_BUFFER) {
		return GENERIC_ERROR;
	}

	memcpy(shadowRxBuf, params.MessageParams.pPayload, params.MessageParams.PayloadLen);
	shadowRxBuf[params.MessageParams.PayloadLen] = '\0';	// jsmn_parse relies on a string

	if (!isJsonValidAndParse(shadowRxBuf, pJsonHandler, &tokenCount)) {
		WARN("Received JSON is not valid");
		return GENERIC_ERROR;
	}

	if (isAckForMyThingName(params.pTopicName)) {
		uint32_t tempVersionNumber = 0;
		if (extractVersionNumber(shadowRxBuf, pJsonHandler, tokenCount, &tempVersionNumber)) {
			if (tempVersionNumber > shadowJsonVersionNum) {
				shadowJsonVersionNum = tempVersionNumber;
			}
		}
	}

	if (extractClientToken(shadowRxBuf, temporaryClientToken)) {
		for (i = 0; i < MAX_ACKS_TO_COMEIN_AT_ANY_GIVEN_TIME; i++) {
			if (!AckWaitList[i].isFree) {
				if (strcmp(AckWaitList[i].clientTokenID, temporaryClientToken) == 0) {
					Shadow_Ack_Status_t status;
					if (strstr(params.pTopicName, "accepted") != NULL) {
						status = SHADOW_ACK_ACCEPTED;
					} else if (strstr(params.pTopicName, "rejected") != NULL) {
						status = SHADOW_ACK_REJECTED;
					}
					if (status == SHADOW_ACK_ACCEPTED || status == SHADOW_ACK_REJECTED) {
						if (AckWaitList[i].callback != NULL) {
							AckWaitList[i].callback(AckWaitList[i].thingName, AckWaitList[i].action, status,
									shadowRxBuf, AckWaitList[i].pCallbackContext);
						}
						unsubscribeFromAcceptedAndRejected(i);
						AckWaitList[i].isFree = true;
						return NONE_ERROR;
					}
				}
			}
		}
	}

	return GENERIC_ERROR;
}

static int16_t findIndexOfSubscriptionList(const char *pTopic) {
	uint8_t i;
	for (i = 0; i < MAX_TOPICS_AT_ANY_GIVEN_TIME; i++) {
		if (!SubscriptionList[i].isFree) {
			if ((strcmp(pTopic, SubscriptionList[i].Topic) == 0)) {
				return i;
			}
		}
	}
	return -1;
}

static void unsubscribeFromAcceptedAndRejected(uint8_t index) {

	char TemporaryTopicNameAccepted[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	char TemporaryTopicNameRejected[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	IoT_Error_t ret_val = NONE_ERROR;

	topicNameFromThingAndAction(TemporaryTopicNameAccepted, AckWaitList[index].thingName, AckWaitList[index].action,
			SHADOW_ACCEPTED);
	topicNameFromThingAndAction(TemporaryTopicNameRejected, AckWaitList[index].thingName, AckWaitList[index].action,
			SHADOW_REJECTED);

	int16_t indexSubList;

	indexSubList = findIndexOfSubscriptionList(TemporaryTopicNameAccepted);
	if ((indexSubList >= 0)) {
		if (!SubscriptionList[indexSubList].isSticky && (SubscriptionList[indexSubList].count == 1)) {
			ret_val = pMqttClient->unsubscribe(TemporaryTopicNameAccepted);
			if (ret_val == NONE_ERROR) {
				SubscriptionList[indexSubList].isFree = true;
			}
		} else if (SubscriptionList[indexSubList].count > 1) {
			SubscriptionList[indexSubList].count--;
		}
	}

	indexSubList = findIndexOfSubscriptionList(TemporaryTopicNameRejected);
	if ((indexSubList >= 0)) {
		if (!SubscriptionList[indexSubList].isSticky && (SubscriptionList[indexSubList].count == 1)) {
			ret_val = pMqttClient->unsubscribe(TemporaryTopicNameRejected);
			if (ret_val == NONE_ERROR) {
				SubscriptionList[indexSubList].isFree = true;
			}
		} else if (SubscriptionList[indexSubList].count > 1) {
			SubscriptionList[indexSubList].count--;
		}
	}
}

void initializeRecords(MQTTClient_t *pClient) {
	uint8_t i;
	for (i = 0; i < MAX_ACKS_TO_COMEIN_AT_ANY_GIVEN_TIME; i++) {
		AckWaitList[i].isFree = true;
	}
	for (i = 0; i < MAX_TOPICS_AT_ANY_GIVEN_TIME; i++) {
		SubscriptionList[i].isFree = true;
		SubscriptionList[i].count = 0;
		SubscriptionList[i].isSticky = false;
	}
	pMqttClient = pClient;
}

bool isSubscriptionPresent(const char *pThingName, ShadowActions_t action) {

	uint8_t i = 0;
	bool isAcceptedPresent = false;
	bool isRejectedPresent = false;
	char TemporaryTopicNameAccepted[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	char TemporaryTopicNameRejected[MAX_SHADOW_TOPIC_LENGTH_BYTES];

	topicNameFromThingAndAction(TemporaryTopicNameAccepted, pThingName, action, SHADOW_ACCEPTED);
	topicNameFromThingAndAction(TemporaryTopicNameRejected, pThingName, action, SHADOW_REJECTED);

	for (i = 0; i < MAX_TOPICS_AT_ANY_GIVEN_TIME; i++) {
		if (!SubscriptionList[i].isFree) {
			if ((strcmp(TemporaryTopicNameAccepted, SubscriptionList[i].Topic) == 0)) {
				isAcceptedPresent = true;
			} else if ((strcmp(TemporaryTopicNameRejected, SubscriptionList[i].Topic) == 0)) {
				isRejectedPresent = true;
			}
		}
	}

	if (isRejectedPresent && isAcceptedPresent) {
		return true;
	}

	return false;
}

IoT_Error_t subscribeToShadowActionAcks(const char *pThingName, ShadowActions_t action, bool isSticky) {
	IoT_Error_t ret_val = NONE_ERROR;
	MQTTSubscribeParams subParams = MQTTSubscribeParamsDefault;

	bool clearBothEntriesFromList = true;
	int16_t indexAcceptedSubList = 0;
	int16_t indexRejectedSubList = 0;
	indexAcceptedSubList = getNextFreeIndexOfSubscriptionList();
	indexRejectedSubList = getNextFreeIndexOfSubscriptionList();

	if (indexAcceptedSubList >= 0 && indexRejectedSubList >= 0) {
		topicNameFromThingAndAction(SubscriptionList[indexAcceptedSubList].Topic, pThingName, action, SHADOW_ACCEPTED);
		subParams.mHandler = AckStatusCallback;
		subParams.qos = QOS_0;
		subParams.pTopic = SubscriptionList[indexAcceptedSubList].Topic;
		ret_val = pMqttClient->subscribe(&subParams);
		if (ret_val == NONE_ERROR) {
			SubscriptionList[indexAcceptedSubList].count = 1;
			SubscriptionList[indexAcceptedSubList].isSticky = isSticky;
			topicNameFromThingAndAction(SubscriptionList[indexRejectedSubList].Topic, pThingName, action,
					SHADOW_REJECTED);
			subParams.pTopic = SubscriptionList[indexRejectedSubList].Topic;
			ret_val = pMqttClient->subscribe(&subParams);
			if (ret_val == NONE_ERROR) {
				SubscriptionList[indexRejectedSubList].count = 1;
				SubscriptionList[indexRejectedSubList].isSticky = isSticky;
				clearBothEntriesFromList = false;

				// wait for SUBSCRIBE_SETTLING_TIME seconds to let the subscription take effect
				Timer subSettlingtimer;
				InitTimer(&subSettlingtimer);
				countdown(&subSettlingtimer, SUBSCRIBE_SETTLING_TIME);
				while(!expired(&subSettlingtimer));

			}
		}
	}

	if (clearBothEntriesFromList) {
		if (indexAcceptedSubList >= 0) {
			SubscriptionList[indexAcceptedSubList].isFree = true;
		} else if (indexRejectedSubList >= 0) {
			SubscriptionList[indexRejectedSubList].isFree = true;
		}
		if (SubscriptionList[indexAcceptedSubList].count == 1) {
			pMqttClient->unsubscribe(SubscriptionList[indexAcceptedSubList].Topic);
		}
	}

	return ret_val;
}

void incrementSubscriptionCnt(const char *pThingName, ShadowActions_t action, bool isSticky) {
	char TemporaryTopicNameAccepted[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	char TemporaryTopicNameRejected[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	uint8_t i;
	topicNameFromThingAndAction(TemporaryTopicNameAccepted, pThingName, action, SHADOW_ACCEPTED);
	topicNameFromThingAndAction(TemporaryTopicNameRejected, pThingName, action, SHADOW_REJECTED);

	for (i = 0; i < MAX_TOPICS_AT_ANY_GIVEN_TIME; i++) {
		if (!SubscriptionList[i].isFree) {
			if ((strcmp(TemporaryTopicNameAccepted, SubscriptionList[i].Topic) == 0)
					|| (strcmp(TemporaryTopicNameRejected, SubscriptionList[i].Topic) == 0)) {
				SubscriptionList[i].count++;
				SubscriptionList[i].isSticky = isSticky;
			}
		}
	}
}

IoT_Error_t publishToShadowAction(const char * pThingName, ShadowActions_t action, const char *pJsonDocumentToBeSent) {
	IoT_Error_t ret_val = NONE_ERROR;
	char TemporaryTopicName[MAX_SHADOW_TOPIC_LENGTH_BYTES];
	topicNameFromThingAndAction(TemporaryTopicName, pThingName, action, SHADOW_ACTION);

	MQTTPublishParams pubParams = MQTTPublishParamsDefault;
	pubParams.pTopic = TemporaryTopicName;
	MQTTMessageParams msgParams = MQTTMessageParamsDefault;
	msgParams.qos = QOS_0;
	msgParams.PayloadLen = strlen(pJsonDocumentToBeSent) + 1;
	msgParams.pPayload = (char *) pJsonDocumentToBeSent;
	pubParams.MessageParams = msgParams;
	ret_val = pMqttClient->publish(&pubParams);

	return ret_val;
}

bool getNextFreeIndexOfAckWaitList(uint8_t *pIndex) {
	uint8_t i;
	if (pIndex != NULL) {
		for (i = 0; i < MAX_ACKS_TO_COMEIN_AT_ANY_GIVEN_TIME; i++) {
			if (AckWaitList[i].isFree) {
				*pIndex = i;
				return true;
			}
		}
	}
	return false;
}

void addToAckWaitList(uint8_t indexAckWaitList, const char *pThingName, ShadowActions_t action,
		const char *pExtractedClientToken, fpActionCallback_t callback, void *pCallbackContext,
		uint32_t timeout_seconds) {
	AckWaitList[indexAckWaitList].callback = callback;
	strncpy(AckWaitList[indexAckWaitList].clientTokenID, pExtractedClientToken, MAX_SIZE_CLIENT_ID_WITH_SEQUENCE);
	strncpy(AckWaitList[indexAckWaitList].thingName, pThingName, MAX_SIZE_OF_THING_NAME);
	AckWaitList[indexAckWaitList].pCallbackContext = pCallbackContext;
	AckWaitList[indexAckWaitList].action = action;
	InitTimer(&(AckWaitList[indexAckWaitList].timer));
	countdown(&(AckWaitList[indexAckWaitList].timer), timeout_seconds);
	AckWaitList[indexAckWaitList].isFree = false;
}

void HandleExpiredResponseCallbacks(void) {
	uint8_t i;
	for (i = 0; i < MAX_ACKS_TO_COMEIN_AT_ANY_GIVEN_TIME; i++) {
		if (!AckWaitList[i].isFree) {
			if (expired(&(AckWaitList[i].timer))) {
				if (AckWaitList[i].callback != NULL) {
					AckWaitList[i].callback(AckWaitList[i].thingName, AckWaitList[i].action, SHADOW_ACK_TIMEOUT,
							shadowRxBuf, AckWaitList[i].pCallbackContext);
				}
				AckWaitList[i].isFree = true;
				unsubscribeFromAcceptedAndRejected(i);
			}
		}
	}
}

static int shadow_delta_callback(MQTTCallbackParams params) {

	int32_t tokenCount;
	uint32_t i = 0;
	void *pJsonHandler;
	int32_t DataPosition;
	uint32_t dataLength;

	if (params.MessageParams.PayloadLen > SHADOW_MAX_SIZE_OF_RX_BUFFER) {
		return GENERIC_ERROR;
	}

	memcpy(shadowRxBuf, params.MessageParams.pPayload, params.MessageParams.PayloadLen);
	shadowRxBuf[params.MessageParams.PayloadLen] = '\0';	// jsmn_parse relies on a string

	if (!isJsonValidAndParse(shadowRxBuf, pJsonHandler, &tokenCount)) {
		WARN("Received JSON is not valid");
		return GENERIC_ERROR;
	}

	if (shadowDiscardOldDeltaFlag) {
		uint32_t tempVersionNumber = 0;
		if (extractVersionNumber(shadowRxBuf, pJsonHandler, tokenCount, &tempVersionNumber)) {
			if (tempVersionNumber > shadowJsonVersionNum) {
				shadowJsonVersionNum = tempVersionNumber;
				DEBUG("New Version number: %d", shadowJsonVersionNum);
			} else {
				WARN("Old Delta Message received - Ignoring rx: %d local: %d", tempVersionNumber, shadowJsonVersionNum);
				return GENERIC_ERROR;
			}
		}
	}

	for (i = 0; i < tokenTableIndex; i++) {
		if (!tokenTable[i].isFree) {
			if (isJsonKeyMatchingAndUpdateValue(shadowRxBuf, pJsonHandler, tokenCount, tokenTable[i].pStruct,
					&dataLength, &DataPosition)) {
				if (tokenTable[i].callback != NULL) {
					tokenTable[i].callback(shadowRxBuf + DataPosition, dataLength, tokenTable[i].pStruct);
				}
			}
		}
	}

	return NONE_ERROR;
}
