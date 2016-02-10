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

#include "aws_iot_shadow_json.h"

#include <string.h>
#include <stdbool.h>
#include <inttypes.h>
#include "aws_iot_json_utils.h"
#include "aws_iot_log.h"
#include "aws_iot_shadow_key.h"
#include "aws_iot_config.h"

extern char mqttClientID[MAX_SIZE_OF_UNIQUE_CLIENT_ID_BYTES];

static uint32_t clientTokenNum = 0;

//helper functions
static IoT_Error_t convertDataToString(char *pStringBuffer, size_t maxSizoStringBuffer, JsonPrimitiveType type,
		void *pData);

void resetClientTokenSequenceNum(void) {
	clientTokenNum = 0;
}

static void emptyJsonWithClientToken(char *pJsonDocument) {
	sprintf(pJsonDocument, "{\"clientToken\":\"");
	FillWithClientToken(pJsonDocument + strlen(pJsonDocument));
	sprintf(pJsonDocument + strlen(pJsonDocument), "\"}");
}

void iot_shadow_get_request_json(char *pJsonDocument) {
	emptyJsonWithClientToken(pJsonDocument);
}

void iot_shadow_delete_request_json(char *pJsonDocument) {
	emptyJsonWithClientToken(pJsonDocument);
}

static inline IoT_Error_t checkReturnValueOfSnPrintf(int32_t snPrintfReturn, size_t maxSizeOfJsonDocument) {

	if (snPrintfReturn >= maxSizeOfJsonDocument) {
		return SHADOW_JSON_BUFFER_TRUNCATED;
	} else if (snPrintfReturn < 0) {
		return SHADOW_JSON_ERROR;
	}
	return NONE_ERROR;
}

IoT_Error_t aws_iot_shadow_init_json_document(char *pJsonDocument, size_t maxSizeOfJsonDocument) {

	IoT_Error_t ret_val = NONE_ERROR;
	int32_t snPrintfReturn = 0;

	if (pJsonDocument == NULL) {
		return NULL_VALUE_ERROR;
	}
	snPrintfReturn = snprintf(pJsonDocument, maxSizeOfJsonDocument, "{\"state\":{");

	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, maxSizeOfJsonDocument);

	return ret_val;

}

IoT_Error_t aws_iot_shadow_add_desired(char *pJsonDocument, size_t maxSizeOfJsonDocument, uint8_t count, ...) {
	IoT_Error_t ret_val = NONE_ERROR;
	int32_t tempSize = 0;
	int8_t i;
	size_t remSizeOfJsonBuffer = maxSizeOfJsonDocument;
	int32_t snPrintfReturn = 0;
	va_list pArgs;
	va_start(pArgs, count);
	jsonStruct_t *pTemporary;

	if (pJsonDocument == NULL) {
		return NULL_VALUE_ERROR;
	}

	tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
		if(tempSize <= 1){
			return SHADOW_JSON_ERROR;
		}
		remSizeOfJsonBuffer = tempSize;

	snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer, "\"desired\":{");
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);

	if (ret_val != NONE_ERROR) {
		return ret_val;
	}

	for (i = 0; i < count; i++) {
		tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
			if(tempSize <= 1){
				return SHADOW_JSON_ERROR;
			}
			remSizeOfJsonBuffer = tempSize;
		pTemporary = va_arg (pArgs, jsonStruct_t *);
		if (pTemporary != NULL) {
			snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer, "\"%s\":",
					pTemporary->pKey);
			ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);
			if (ret_val != NONE_ERROR) {
				return ret_val;
			}
			if (pTemporary->pKey != NULL && pTemporary->pData != NULL) {
				ret_val = convertDataToString(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer,
						pTemporary->type, pTemporary->pData);
			} else {
				return NULL_VALUE_ERROR;
			}
			if (ret_val != NONE_ERROR) {
				return ret_val;
			}
		} else {
			return NULL_VALUE_ERROR;
		}
	}

	va_end(pArgs);
	snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument) - 1, remSizeOfJsonBuffer, "},");
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);
	return ret_val;
}

IoT_Error_t aws_iot_shadow_add_reported(char *pJsonDocument, size_t maxSizeOfJsonDocument, uint8_t count, ...) {
	IoT_Error_t ret_val = NONE_ERROR;

	int8_t i;
	size_t remSizeOfJsonBuffer = maxSizeOfJsonDocument;
	int32_t snPrintfReturn = 0;
	int32_t tempSize = 0;
	va_list pArgs;
	va_start(pArgs, count);
	jsonStruct_t *pTemporary;

	if (pJsonDocument == NULL) {
		return NULL_VALUE_ERROR;
	}


	tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
	if(tempSize <= 1){
		return SHADOW_JSON_ERROR;
	}
	remSizeOfJsonBuffer = tempSize;

	snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer, "\"reported\":{");
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);

	if (ret_val != NONE_ERROR) {
		return ret_val;
	}

	for (i = 0; i < count; i++) {
		tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
		if(tempSize <= 1){
			return SHADOW_JSON_ERROR;
		}
		remSizeOfJsonBuffer = tempSize;

		pTemporary = va_arg (pArgs, jsonStruct_t *);
		if (pTemporary != NULL) {
			snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer, "\"%s\":",
					pTemporary->pKey);
			ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);
			if (ret_val != NONE_ERROR) {
				return ret_val;
			}
			if (pTemporary->pKey != NULL && pTemporary->pData != NULL) {
				ret_val = convertDataToString(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer,
						pTemporary->type, pTemporary->pData);
			} else {
				return NULL_VALUE_ERROR;
			}
			if (ret_val != NONE_ERROR) {
				return ret_val;
			}
		} else {
			return NULL_VALUE_ERROR;
		}
	}

	va_end(pArgs);
	snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument) - 1, remSizeOfJsonBuffer, "},");
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);
	return ret_val;
}


int32_t FillWithClientTokenSize(char *pBufferToBeUpdatedWithClientToken, size_t maxSizeOfJsonDocument) {
	int32_t snPrintfReturn;
	snPrintfReturn = snprintf(pBufferToBeUpdatedWithClientToken, maxSizeOfJsonDocument, "%s-%d", mqttClientID,
			clientTokenNum++);

	return snPrintfReturn;
}

IoT_Error_t aws_iot_fill_with_client_token(char *pBufferToBeUpdatedWithClientToken, size_t maxSizeOfJsonDocument){

	int32_t snPrintfRet = 0;
	snPrintfRet = FillWithClientTokenSize(pBufferToBeUpdatedWithClientToken, maxSizeOfJsonDocument);
	return checkReturnValueOfSnPrintf(snPrintfRet, maxSizeOfJsonDocument);

}

IoT_Error_t aws_iot_finalize_json_document(char *pJsonDocument, size_t maxSizeOfJsonDocument) {
	size_t remSizeOfJsonBuffer = maxSizeOfJsonDocument;
	int32_t snPrintfReturn = 0;
	int32_t tempSize = 0;
	IoT_Error_t ret_val = NONE_ERROR;

	if (pJsonDocument == NULL) {
		return NULL_VALUE_ERROR;
	}

	tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
	if(tempSize <= 1){
		return SHADOW_JSON_ERROR;
	}
	remSizeOfJsonBuffer = tempSize;

	// strlen(ShadowTxBuffer) - 1 is to ensure we remove the last ,(comma) that was added
	snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument) - 1, remSizeOfJsonBuffer, "}, \"%s\":\"",
			SHADOW_CLIENT_TOKEN_STRING);
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);

	if (ret_val != NONE_ERROR) {
		return ret_val;
	}
	// refactor this XXX repeated code
	tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
	if(tempSize <= 1){
		return SHADOW_JSON_ERROR;
	}
	remSizeOfJsonBuffer = tempSize;


	snPrintfReturn = FillWithClientTokenSize(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer);
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);

	if (ret_val != NONE_ERROR) {
		return ret_val;
	}
	tempSize = maxSizeOfJsonDocument - strlen(pJsonDocument);
	if(tempSize <= 1){
		return SHADOW_JSON_ERROR;
	}
	remSizeOfJsonBuffer = tempSize;


	snPrintfReturn = snprintf(pJsonDocument + strlen(pJsonDocument), remSizeOfJsonBuffer, "\"}");
	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, remSizeOfJsonBuffer);

	return ret_val;
}

void FillWithClientToken(char *pBufferToBeUpdatedWithClientToken) {
	sprintf(pBufferToBeUpdatedWithClientToken, "%s-%d", mqttClientID, clientTokenNum++);
}

static IoT_Error_t convertDataToString(char *pStringBuffer, size_t maxSizoStringBuffer, JsonPrimitiveType type,
		void *pData) {
	int32_t snPrintfReturn = 0;
	IoT_Error_t ret_val = NONE_ERROR;

	if (maxSizoStringBuffer == 0) {
		return SHADOW_JSON_ERROR;
	}

	if (type == SHADOW_JSON_INT32) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%"PRIi32",", *(int32_t * )(pData));
	} else if (type == SHADOW_JSON_INT16) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%"PRIi16",", *(int16_t * )(pData));
	} else if (type == SHADOW_JSON_INT8) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%"PRIi8",", *(int8_t * )(pData));
	} else if (type == SHADOW_JSON_UINT32) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%"PRIu32",", *(uint32_t * )(pData));
	} else if (type == SHADOW_JSON_UINT16) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%"PRIu16",", *(uint16_t * )(pData));
	} else if (type == SHADOW_JSON_UINT8) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%"PRIu8",", *(uint8_t * )(pData));
	} else if (type == SHADOW_JSON_DOUBLE) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%f,", *(double * )(pData));
	} else if (type == SHADOW_JSON_FLOAT) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%f,", *(float * )(pData));
	} else if (type == SHADOW_JSON_BOOL) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "%s,", *(bool *)(pData)?"true":"false");
	} else if (type == SHADOW_JSON_STRING) {
		snPrintfReturn = snprintf(pStringBuffer, maxSizoStringBuffer, "\"%s\",", (char * )(pData));
	}

	ret_val = checkReturnValueOfSnPrintf(snPrintfReturn, maxSizoStringBuffer);

	return ret_val;
}
static jsmn_parser shadowJsonParser;
static jsmntok_t jsonTokenStruct[MAX_JSON_TOKEN_EXPECTED];

bool isJsonValidAndParse(const char *pJsonDocument, void *pJsonHandler, int32_t *pTokenCount) {
	int32_t tokenCount;

	jsmn_init(&shadowJsonParser);

	tokenCount = jsmn_parse(&shadowJsonParser, pJsonDocument, strlen(pJsonDocument), jsonTokenStruct,
			sizeof(jsonTokenStruct) / sizeof(jsonTokenStruct[0]));

	if (tokenCount < 0) {
		WARN("Failed to parse JSON: %d\n", tokenCount);
		return false;
	}

	/* Assume the top-level element is an object */
	if (tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		WARN("Top Level is not an object\n");
		return false;
	}

	pJsonHandler = (void *) jsonTokenStruct;
	*pTokenCount = tokenCount;

	return true;
}

static IoT_Error_t UpdateValueIfNoObject(const char *pJsonString, jsonStruct_t *pDataStruct, jsmntok_t token) {
	IoT_Error_t ret_val = NONE_ERROR;
	if (pDataStruct->type == SHADOW_JSON_BOOL) {
		ret_val = parseBooleanValue(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_INT32) {
		ret_val = parseInteger32Value(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_INT16) {
		ret_val = parseInteger16Value(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_INT8) {
		ret_val = parseInteger8Value(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_UINT32) {
		ret_val = parseUnsignedInteger32Value(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_UINT16) {
		ret_val = parseUnsignedInteger16Value(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_UINT8) {
		ret_val = parseUnsignedInteger8Value(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_FLOAT) {
		ret_val = parseFloatValue(pDataStruct->pData, pJsonString, &token);
	} else if (pDataStruct->type == SHADOW_JSON_DOUBLE) {
		ret_val = parseDoubleValue(pDataStruct->pData, pJsonString, &token);
	}

	return ret_val;
}

bool isJsonKeyMatchingAndUpdateValue(const char *pJsonDocument, void *pJsonHandler, int32_t tokenCount,
		jsonStruct_t *pDataStruct, uint32_t *pDataLength, int32_t *pDataPosition) {
	int32_t i;

	jsmntok_t *pJsonTokenStruct;

	pJsonTokenStruct = (jsmntok_t *) pJsonHandler;
	for (i = 1; i < tokenCount; i++) {
		if (jsoneq(pJsonDocument, &(jsonTokenStruct[i]), pDataStruct->pKey) == 0) {
			jsmntok_t dataToken = jsonTokenStruct[i + 1];
			uint32_t dataLength = dataToken.end - dataToken.start;
			UpdateValueIfNoObject(pJsonDocument, pDataStruct, dataToken);
			*pDataPosition = dataToken.start;
			*pDataLength = dataLength;
			return true;
		}
	}
	return false;
}

bool isReceivedJsonValid(const char *pJsonDocument) {
	int32_t tokenCount;

	jsmn_init(&shadowJsonParser);

	tokenCount = jsmn_parse(&shadowJsonParser, pJsonDocument, strlen(pJsonDocument), jsonTokenStruct,
			sizeof(jsonTokenStruct) / sizeof(jsonTokenStruct[0]));

	if (tokenCount < 0) {
		WARN("Failed to parse JSON: %d\n", tokenCount);
		return false;
	}

	/* Assume the top-level element is an object */
	if (tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		return false;
	}

	return true;
}

bool extractClientToken(const char *pJsonDocument, char *pExtractedClientToken) {
	bool ret_val = false;
	jsmn_init(&shadowJsonParser);
	int32_t tokenCount, i;
	jsmntok_t ClientJsonToken;

	tokenCount = jsmn_parse(&shadowJsonParser, pJsonDocument, strlen(pJsonDocument), jsonTokenStruct,
			sizeof(jsonTokenStruct) / sizeof(jsonTokenStruct[0]));

	if (tokenCount < 0) {
		WARN("Failed to parse JSON: %d\n", tokenCount);
		return false;
	}

	/* Assume the top-level element is an object */
	if (tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		return false;
	}

	for (i = 1; i < tokenCount; i++) {
		if (jsoneq(pJsonDocument, &jsonTokenStruct[i], SHADOW_CLIENT_TOKEN_STRING) == 0) {
			ClientJsonToken = jsonTokenStruct[i + 1];
			uint8_t length = ClientJsonToken.end - ClientJsonToken.start;
			strncpy(pExtractedClientToken, pJsonDocument + ClientJsonToken.start, length);
			pExtractedClientToken[length] = '\0';
			return true;
		}
	}

	return false;
}

bool extractVersionNumber(const char *pJsonDocument, void *pJsonHandler, int32_t tokenCount, uint32_t *pVersionNumber) {
	int32_t i;
	jsmntok_t *pJsonTokenStruct;
	IoT_Error_t ret_val = NONE_ERROR;

	pJsonTokenStruct = (jsmntok_t *) pJsonHandler;
	for (i = 1; i < tokenCount; i++) {
		if (jsoneq(pJsonDocument, &(jsonTokenStruct[i]), SHADOW_VERSION_STRING) == 0) {
			jsmntok_t dataToken = jsonTokenStruct[i + 1];
			uint32_t dataLength = dataToken.end - dataToken.start;
			ret_val = parseUnsignedInteger32Value(pVersionNumber, pJsonDocument, &dataToken);
			if (ret_val == NONE_ERROR) {
				return true;
			}
		}
	}
	return false;
}

