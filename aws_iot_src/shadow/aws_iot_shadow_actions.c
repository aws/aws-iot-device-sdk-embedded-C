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

#include "aws_iot_shadow_actions.h"

#include "aws_iot_log.h"
#include "aws_iot_shadow_json.h"
#include "aws_iot_shadow_records.h"
#include "aws_iot_config.h"

IoT_Error_t iot_shadow_action(MQTTClient_t *pClient, const char *pThingName, ShadowActions_t action,
		const char *pJsonDocumentToBeSent, fpActionCallback_t callback, void *pCallbackContext,
		uint32_t timeout_seconds, bool isSticky) {

	IoT_Error_t ret_val = NONE_ERROR;
	bool isCallbackPresent = false;
	bool isClientTokenPresent = false;
	bool isAckWaitListFree = false;
	uint8_t indexAckWaitList;

	if(pClient == NULL || pThingName == NULL || pJsonDocumentToBeSent == NULL){
		return NULL_VALUE_ERROR;
	}

	if (getNextFreeIndexOfAckWaitList(&indexAckWaitList)) {
		isAckWaitListFree = true;
	}
	if (callback != NULL) {
		isCallbackPresent = true;
	}

	char extractedClientToken[MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE];
	isClientTokenPresent = extractClientToken(pJsonDocumentToBeSent, extractedClientToken);

	if (isClientTokenPresent && isCallbackPresent && isAckWaitListFree) {
		if (!isSubscriptionPresent(pThingName, action)) {
			ret_val = subscribeToShadowActionAcks(pThingName, action, isSticky);
		} else {
			incrementSubscriptionCnt(pThingName, action, isSticky);
		}
	}


	if (ret_val == NONE_ERROR) {
		ret_val = publishToShadowAction(pThingName, action, pJsonDocumentToBeSent);
	}

	if (isClientTokenPresent && isCallbackPresent && ret_val == NONE_ERROR && isAckWaitListFree) {
		addToAckWaitList(indexAckWaitList, pThingName, action, extractedClientToken, callback, pCallbackContext,
				timeout_seconds);
	}
	return ret_val;
}
