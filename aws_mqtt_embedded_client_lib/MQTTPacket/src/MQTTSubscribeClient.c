/*******************************************************************************
 * Copyright (c) 2014 IBM Corp.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * and Eclipse Distribution License v1.0 which accompany this distribution.
 *
 * The Eclipse Public License is available at
 *    http://www.eclipse.org/legal/epl-v10.html
 * and the Eclipse Distribution License is available at
 *   http://www.eclipse.org/org/documents/edl-v10.php.
 *
 * Contributors:
 *    Ian Craggs - initial API and implementation and/or initial documentation
 *******************************************************************************/

#include "MQTTPacket.h"
#include "StackTrace.h"

#include <string.h>

/**
  * Determines the length of the MQTT subscribe packet that would be produced using the supplied parameters
  * @param count the number of topic filter strings in topicFilters
  * @param topicFilters the array of topic filter strings to be used in the publish
  * @return the length of buffer needed to contain the serialized version of the packet
  */
size_t MQTTSerialize_GetSubscribePacketLength(uint32_t count, MQTTString topicFilters[]) {
	size_t i;
	size_t len = 2; /* packetid */

	for(i = 0; i < count; ++i) {
		len += 2 + MQTTstrlen(topicFilters[i]) + 1; /* length + topic + req_qos */
	}

	return len;
}

/**
  * Serializes the supplied subscribe data into the supplied buffer, ready for sending
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied bufferr
  * @param dup integer - the MQTT dup flag
  * @param packetid integer - the MQTT packet identifier
  * @param count - number of members in the topicFilters and reqQos arrays
  * @param topicFilters - array of topic filter names
  * @param requestedQoSs - array of requested QoS
  * @return the length of the serialized data.  <= 0 indicates error
  */
MQTTReturnCode MQTTSerialize_subscribe(unsigned char *buf, size_t buflen,
									   unsigned char dup, uint16_t packetid, uint32_t count,
									   MQTTString topicFilters[], QoS requestedQoSs[],
									   uint32_t *serialized_len) {
        unsigned char *ptr = buf;
        MQTTHeader header = {0};
        size_t rem_len = 0;
        uint32_t i = 0;
        MQTTReturnCode rc = MQTTPacket_InitHeader(&header, SUBSCRIBE, 1, dup, 0);
	FUNC_ENTRY;
	if(NULL == buf || NULL == serialized_len) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	if(MQTTPacket_len(rem_len = MQTTSerialize_GetSubscribePacketLength(count, topicFilters)) > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}
	/* write header */
	writeChar(&ptr, header.byte);

	/* write remaining length */
	ptr += MQTTPacket_encode(ptr, rem_len);

	writePacketId(&ptr, packetid);

	for(i = 0; i < count; ++i) {
		writeMQTTString(&ptr, topicFilters[i]);
		writeChar(&ptr, (unsigned char)requestedQoSs[i]);
	}

	*serialized_len = (uint32_t)(ptr - buf);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

/**
  * Deserializes the supplied (wire) buffer into suback data
  * @param packetid returned integer - the MQTT packet identifier
  * @param maxcount - the maximum number of members allowed in the grantedQoSs array
  * @param count returned integer - number of members in the grantedQoSs array
  * @param grantedQoSs returned array of integers - the granted qualities of service
  * @param buf the raw buffer data, of the correct length determined by the remaining length field
  * @param buflen the length in bytes of the data in the supplied buffer
  * @return error code.  1 is success, 0 is failure
  */
MQTTReturnCode MQTTDeserialize_suback(uint16_t *packetid, uint32_t maxcount,
									  uint32_t *count, QoS grantedQoSs[],
									  unsigned char *buf, size_t buflen) {
        MQTTHeader header = {0};
        unsigned char *curdata = buf;
        unsigned char *enddata = NULL;
        MQTTReturnCode decodeRc = FAILURE;
        uint32_t decodedLen = 0;
        uint32_t readBytesLen = 0;

	FUNC_ENTRY;
	if(NULL == packetid || NULL == count || NULL == grantedQoSs) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	/* SUBACK header size is 4 bytes for header and at least one byte for QoS payload
	 * Need at least a 5 bytes buffer. MQTT3.1.1 specification 3.9
	 */
	if(5 > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	header.byte = readChar(&curdata);
	if (header.bits.type != SUBACK) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

	/* read remaining length */
	decodeRc = MQTTPacket_decodeBuf(curdata, &decodedLen, &readBytesLen);
	if(decodeRc != SUCCESS) {
		return decodeRc;
	}

	curdata += (readBytesLen);
	enddata = curdata + decodedLen;
	if (enddata - curdata < 2) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

	*packetid = readPacketId(&curdata);

	*count = 0;
	while(curdata < enddata) {
		if(*count > maxcount) {
			FUNC_EXIT_RC(FAILURE);
			return FAILURE;
		}
		grantedQoSs[(*count)++] = (QoS)readChar(&curdata);
	}

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}
