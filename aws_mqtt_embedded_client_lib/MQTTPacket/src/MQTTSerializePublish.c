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
 *    Ian Craggs - fix for https://bugs.eclipse.org/bugs/show_bug.cgi?id=453144
 *******************************************************************************/

#include "MQTTPacket.h"
#include "StackTrace.h"

#include <string.h>


/**
  * Determines the length of the MQTT publish packet that would be produced using the supplied parameters
  * @param qos the MQTT QoS of the publish (packetid is omitted for QoS 0)
  * @param topicName the topic name to be used in the publish  
  * @param payloadlen the length of the payload to be sent
  * @return the length of buffer needed to contain the serialized version of the packet
  */
size_t MQTTSerialize_GetPublishLength(uint8_t qos, MQTTString topicName, size_t payloadlen) {
	size_t len = 0;

	len += 2 + MQTTstrlen(topicName) + payloadlen;
	if(qos > 0) {
		len += 2; /* packetid */
	}
	return len;
}


/**
  * Serializes the supplied publish data into the supplied buffer, ready for sending
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer
  * @param dup integer - the MQTT dup flag
  * @param qos integer - the MQTT QoS value
  * @param retained integer - the MQTT retained flag
  * @param packetid integer - the MQTT packet identifier
  * @param topicName MQTTString - the MQTT topic in the publish
  * @param payload byte buffer - the MQTT publish payload
  * @param payloadlen integer - the length of the MQTT payload
  * @return the length of the serialized data.  <= 0 indicates error
  */
MQTTReturnCode MQTTSerialize_publish(unsigned char *buf, size_t buflen, uint8_t dup,
						  QoS qos, uint8_t retained, uint16_t packetid,
						  MQTTString topicName, unsigned char *payload, size_t payloadlen,
						  uint32_t *serialized_len) {
        unsigned char *ptr = buf;
        MQTTHeader header = {0};
        size_t rem_len = 0;
        MQTTReturnCode rc = MQTTPacket_InitHeader(&header, PUBLISH, qos, dup, retained);

	FUNC_ENTRY;
	if(NULL == buf || NULL == payload || NULL == serialized_len) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	rem_len = MQTTSerialize_GetPublishLength(qos, topicName, payloadlen);
	if(MQTTPacket_len(rem_len) > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}
	writeChar(&ptr, header.byte); /* write header */

	ptr += MQTTPacket_encode(ptr, rem_len); /* write remaining length */;

	writeMQTTString(&ptr, topicName);

	if(qos > 0) {
		writeInt(&ptr, packetid);
	}

	memcpy(ptr, payload, payloadlen);
	ptr += payloadlen;

	*serialized_len = (uint32_t)(ptr - buf);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

/**
  * Serializes the ack packet into the supplied buffer.
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer
  * @param type the MQTT packet type
  * @param dup the MQTT dup flag
  * @param packetid the MQTT packet identifier
  * @return serialized length, or error if 0
  */
MQTTReturnCode MQTTSerialize_ack(unsigned char *buf, size_t buflen,
					  unsigned char type, uint8_t dup, uint16_t packetid,
					  uint32_t *serialized_len) {
        MQTTHeader header = {0};
        unsigned char *ptr = buf;
        QoS requestQoS = (PUBREL == type) ? QOS1 : QOS0;
        MQTTReturnCode rc = MQTTPacket_InitHeader(&header, type, requestQoS, dup, 0);

	FUNC_ENTRY;
	if(NULL == buf || serialized_len == NULL) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	/* Minimum byte length required by ACK headers is
	 * 2 for fixed and 2 for variable part */
	if(4 > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}
	writeChar(&ptr, header.byte); /* write header */

	ptr += MQTTPacket_encode(ptr, 2); /* write remaining length */
	writePacketId(&ptr, packetid);
	*serialized_len = (uint32_t)(ptr - buf);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}


/**
  * Serializes a puback packet into the supplied buffer.
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer
  * @param packetid integer - the MQTT packet identifier
  * @return serialized length, or error if 0
  */
MQTTReturnCode MQTTSerialize_puback(unsigned char* buf, size_t buflen,
									uint16_t packetid, uint32_t *serialized_len) {
	return MQTTSerialize_ack(buf, buflen, PUBACK, 0, packetid, serialized_len);
}


/**
  * Serializes a pubrel packet into the supplied buffer.
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer
  * @param dup integer - the MQTT dup flag
  * @param packetid integer - the MQTT packet identifier
  * @return serialized length, or error if 0
  */
MQTTReturnCode MQTTSerialize_pubrel(unsigned char *buf, size_t buflen,
									unsigned char dup, uint16_t packetid,
									uint32_t *serialized_len) {
	return MQTTSerialize_ack(buf, buflen, PUBREL, dup, packetid, serialized_len);
}


/**
  * Serializes a pubrel packet into the supplied buffer.
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer
  * @param packetid integer - the MQTT packet identifier
  * @return serialized length, or error if 0
  */
MQTTReturnCode MQTTSerialize_pubcomp(unsigned char *buf, size_t buflen,
									 uint16_t packetid, uint32_t *serialized_len) {
	return MQTTSerialize_ack(buf, buflen, PUBCOMP, 0, packetid, serialized_len);
}


