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

#include "StackTrace.h"
#include "MQTTPacket.h"
#include <string.h>

/**
  * Deserializes the supplied (wire) buffer into publish data
  * @param dup returned integer - the MQTT dup flag
  * @param qos returned integer - the MQTT QoS value
  * @param retained returned integer - the MQTT retained flag
  * @param packetid returned integer - the MQTT packet identifier
  * @param topicName returned MQTTString - the MQTT topic in the publish
  * @param payload returned byte buffer - the MQTT publish payload
  * @param payloadlen returned integer - the length of the MQTT payload
  * @param buf the raw buffer data, of the correct length determined by the remaining length field
  * @param buflen the length in bytes of the data in the supplied buffer
  * @return error code.  1 is success
  */
MQTTReturnCode MQTTDeserialize_publish(unsigned char *dup, QoS *qos,
									   unsigned char *retained, uint16_t *packetid,
									   MQTTString* topicName, unsigned char **payload,
									   uint32_t *payloadlen, unsigned char *buf, size_t buflen) {
        MQTTHeader header = {0};
        unsigned char *curdata = buf;
        unsigned char *enddata = NULL;
        MQTTReturnCode rc = FAILURE;
        uint32_t decodedLen = 0;
        uint32_t readBytesLen = 0;

	FUNC_ENTRY;
	if(NULL == dup || NULL == qos || NULL == retained || NULL == packetid) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

	/* Publish header size is at least four bytes.
	 * Fixed header is two bytes.
	 * Variable header size depends on QoS And Topic Name.
	 * QoS level 0 doesn't have a message identifier (0 - 2 bytes)
	 * Topic Name length fields decide size of topic name field (at least 2 bytes)
	 * MQTT v3.1.1 Specification 3.3.1 */
	if(4 > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	header.byte = readChar(&curdata);
	if(PUBLISH != header.bits.type) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

	*dup = header.bits.dup;
	*qos = (QoS)header.bits.qos;
	*retained = header.bits.retain;

	/* read remaining length */
	rc = MQTTPacket_decodeBuf(curdata, &decodedLen, &readBytesLen);
	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}
	curdata += (readBytesLen);
	enddata = curdata + decodedLen;

	/* do we have enough data to read the protocol version byte? */
	if(SUCCESS != readMQTTLenString(topicName, &curdata, enddata) || (0 > (enddata - curdata))) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

	if(QOS0 != *qos) {
		*packetid = readPacketId(&curdata);
	}

	*payloadlen = (uint32_t)(enddata - curdata);
	*payload = curdata;

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

/**
  * Deserializes the supplied (wire) buffer into an ack
  * @param packettype returned integer - the MQTT packet type
  * @param dup returned integer - the MQTT dup flag
  * @param packetid returned integer - the MQTT packet identifier
  * @param buf the raw buffer data, of the correct length determined by the remaining length field
  * @param buflen the length in bytes of the data in the supplied buffer
  * @return error code.  1 is success, 0 is failure
  */
MQTTReturnCode MQTTDeserialize_ack(unsigned char *packettype, unsigned char *dup,
								   uint16_t *packetid, unsigned char *buf,
								   size_t buflen) {
        MQTTReturnCode rc = FAILURE;
        MQTTHeader header = {0};
        unsigned char *curdata = buf;
        unsigned char *enddata = NULL;
        uint32_t decodedLen = 0;
        uint32_t readBytesLen = 0;
	FUNC_ENTRY;
	if(NULL == packettype || NULL == dup || NULL == packetid || NULL == buf) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	/* PUBACK fixed header size is two bytes, variable header is 2 bytes, MQTT v3.1.1 Specification 3.4.1 */
	if(4 > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	header.byte = readChar(&curdata);
	*dup = header.bits.dup;
	*packettype = header.bits.type;

	/* read remaining length */
	rc = MQTTPacket_decodeBuf(curdata, &decodedLen, &readBytesLen);
	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}
	curdata += (readBytesLen);
	enddata = curdata + decodedLen;

	if(enddata - curdata < 2) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

	*packetid = readPacketId(&curdata);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

