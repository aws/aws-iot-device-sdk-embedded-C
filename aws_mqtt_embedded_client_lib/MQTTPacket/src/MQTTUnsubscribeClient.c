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
  * Determines the length of the MQTT unsubscribe packet that would be produced using the supplied parameters
  * @param count the number of topic filter strings in topicFilters
  * @param topicFilters the array of topic filter strings to be used in the publish
  * @return the length of buffer needed to contain the serialized version of the packet
  */
size_t MQTTSerialize_GetUnsubscribePacketLength(uint32_t count, MQTTString topicFilters[]) {
	size_t i;
	size_t len = 2; /* packetid */

	for(i = 0; i < count; ++i) {
		len += 2 + MQTTstrlen(topicFilters[i]); /* length + topic*/
	}

	return len;
}

/**
  * Serializes the supplied unsubscribe data into the supplied buffer, ready for sending
  * @param buf the raw buffer data, of the correct length determined by the remaining length field
  * @param buflen the length in bytes of the data in the supplied buffer
  * @param dup integer - the MQTT dup flag
  * @param packetid integer - the MQTT packet identifier
  * @param count - number of members in the topicFilters array
  * @param topicFilters - array of topic filter names
  * @param serialized_len - the length of the serialized data
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTSerialize_unsubscribe(unsigned char* buf, size_t buflen,
								   uint8_t dup, uint16_t packetid,
								   uint32_t count, MQTTString topicFilters[],
								   uint32_t *serialized_len) {
        unsigned char *ptr = buf;
        MQTTHeader header = {0};
        size_t rem_len = 0;
        uint32_t i = 0;
        MQTTReturnCode rc = MQTTPacket_InitHeader(&header, UNSUBSCRIBE, 1, dup, 0);

	FUNC_ENTRY;
	if(NULL == buf || NULL == serialized_len) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	rem_len = MQTTSerialize_GetUnsubscribePacketLength(count, topicFilters);
	if(MQTTPacket_len(rem_len) > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}
	writeChar(&ptr, header.byte); /* write header */

	ptr += MQTTPacket_encode(ptr, rem_len); /* write remaining length */

	writePacketId(&ptr, packetid);

	for(i = 0; i < count; ++i) {
		writeMQTTString(&ptr, topicFilters[i]);
	}

	*serialized_len = (uint32_t)(ptr - buf);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}


/**
  * Deserializes the supplied (wire) buffer into unsuback data
  * @param packetid returned integer - the MQTT packet identifier
  * @param buf the raw buffer data, of the correct length determined by the remaining length field
  * @param buflen the length in bytes of the data in the supplied buffer
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTDeserialize_unsuback(uint16_t *packetid, unsigned char *buf, size_t buflen) {
        unsigned char type = 0;
        unsigned char dup = 0;
        MQTTReturnCode rc = FAILURE;

	FUNC_ENTRY;
	if(NULL == packetid || NULL == buf) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	rc = MQTTDeserialize_ack(&type, &dup, packetid, buf, buflen);
	if(SUCCESS == rc && UNSUBACK != type) {
		rc = FAILURE;
	}

	FUNC_EXIT_RC(rc);
	return rc;
}
