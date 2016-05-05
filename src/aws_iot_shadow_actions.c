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

IoT_Error_t iot_shadow_action(const char *pThingName, ShadowActions_t action,
		const char *pJsonDocumentToBeSent, fpActionCallback_t callback, void *pCallbackContext,
		uint32_t timeout_seconds, bool isSticky) {

	IoT_Error_t ret_val = SUCCESS;
	bool isCallbackPresent = false;
	bool isClientTokenPresent = false;
	bool isAckWaitListFree = false;
	uint8_t indexAckWaitList;

	if(pThingName == NULL || pJsonDocumentToBeSent == NULL){
		return NULL_VALUE_ERROR;
	}

	if (callback != NULL) {
		isCallbackPresent = true;
	}

	char extractedClientToken[MAX_SIZE_CLIENT_ID_WITH_SEQUENCE];
	isClientTokenPresent = extractClientToken(pJsonDocumentToBeSent, extractedClientToken);

	if (isClientTokenPresent && isCallbackPresent) {
		if (getNextFreeIndexOfAckWaitList(&indexAckWaitList)) {
			isAckWaitListFree = true;
		}

		if(isAckWaitListFree) {
			if (!isSubscriptionPresent(pThingName, action)) {
				ret_val = subscribeToShadowActionAcks(pThingName, action, isSticky);
			} else {
				incrementSubscriptionCnt(pThingName, action, isSticky);
			}
		}
		else {
			ret_val = FAILURE;
		}
	}


	if (ret_val == SUCCESS) {
		ret_val = publishToShadowAction(pThingName, action, pJsonDocumentToBeSent);
	}

	if (isClientTokenPresent && isCallbackPresent && ret_val == SUCCESS && isAckWaitListFree) {
		addToAckWaitList(indexAckWaitList, pThingName, action, extractedClientToken, callback, pCallbackContext,
				timeout_seconds);
	}
	return ret_val;
}
