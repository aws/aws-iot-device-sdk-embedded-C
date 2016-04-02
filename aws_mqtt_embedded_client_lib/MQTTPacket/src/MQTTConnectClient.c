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
  * Determines the length of the MQTT connect packet that would be produced using the supplied connect options.
  * @param options the options to be used to build the connect packet
  * @param the length of buffer needed to contain the serialized version of the packet
  * @return MQTTReturnCode indicating function execution status
  */
size_t MQTTSerialize_GetConnectLength(MQTTPacket_connectData *options) {
        size_t len = 0;
	FUNC_ENTRY;

	/* variable depending on MQTT or MQIsdp */
	if(3 == options->MQTTVersion) {
		len = 12;
	} else if(4 == options->MQTTVersion) {
		len = 10;
	}

	len += MQTTstrlen(options->clientID) + 2;

	if(options->willFlag) {
		len += MQTTstrlen(options->will.topicName) + 2 + MQTTstrlen(options->will.message) + 2;
	}

	if(options->username.cstring || options->username.lenstring.data) {
		len += MQTTstrlen(options->username) + 2;
	}

	if(options->password.cstring || options->password.lenstring.data) {
		len += MQTTstrlen(options->password) + 2;
	}

	FUNC_EXIT_RC(len);
	return len;
}

/**
  * Serializes the connect options into the buffer.
  * @param buf the buffer into which the packet will be serialized
  * @param len the length in bytes of the supplied buffer
  * @param options the options to be used to build the connect packet
  * @param serialized length
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTSerialize_connect(unsigned char *buf, size_t buflen,
									 MQTTPacket_connectData *options,
									 uint32_t *serialized_len) {
        unsigned char *ptr = buf;
        MQTTHeader header = {0};
        MQTTConnectFlags flags = {0};
        size_t len = 0;
        MQTTReturnCode rc = MQTTPacket_InitHeader(&header, CONNECT, QOS0, 0, 0);

	FUNC_ENTRY;
	if(NULL == buf || NULL == options || NULL == serialized_len) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	len = MQTTSerialize_GetConnectLength(options);
	if(MQTTPacket_len(len) > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	if(SUCCESS != rc) {
		FUNC_EXIT_RC(rc);
		return rc;
	}

	writeChar(&ptr, header.byte); /* write header */

	ptr += MQTTPacket_encode(ptr, len); /* write remaining length */

	if(4 == options->MQTTVersion) {
		writeCString(&ptr, "MQTT");
		writeChar(&ptr, (char) 4);
	} else {
		writeCString(&ptr, "MQIsdp");
		writeChar(&ptr, (char) 3);
	}

	flags.all = 0;
	flags.bits.cleansession = (options->cleansession) ? 1 : 0;
	flags.bits.will = (options->willFlag) ? 1 : 0;
	if(flags.bits.will) {
		flags.bits.willQoS = options->will.qos;
		flags.bits.willRetain = (options->will.retained) ? 1 : 0;
	}

	if(options->username.cstring || options->username.lenstring.data) {
		flags.bits.username = 1;
	}

	if(options->password.cstring || options->password.lenstring.data) {
		flags.bits.password = 1;
	}

	writeChar(&ptr, flags.all);
	writeInt(&ptr, options->keepAliveInterval);
	writeMQTTString(&ptr, options->clientID);
	if(options->willFlag) {
		writeMQTTString(&ptr, options->will.topicName);
		writeMQTTString(&ptr, options->will.message);
	}

	if(flags.bits.username) {
		writeMQTTString(&ptr, options->username);
	}

	if(flags.bits.password) {
		writeMQTTString(&ptr, options->password);
	}

	*serialized_len = (uint32_t)(ptr - buf);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

/**
  * Deserializes the supplied (wire) buffer into connack data - return code
  * @param sessionPresent the session present flag returned (only for MQTT 3.1.1)
  * @param connack_rc returned integer value of the connack return code
  * @param buf the raw buffer data, of the correct length determined by the remaining length field
  * @param buflen the length in bytes of the data in the supplied buffer
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTDeserialize_connack(unsigned char *sessionPresent,
									   MQTTReturnCode *connack_rc,
									   unsigned char *buf, size_t buflen) {
        MQTTHeader header = {0};
        unsigned char *curdata = buf;
        unsigned char *enddata = NULL;
        MQTTReturnCode rc = FAILURE;
        uint32_t decodedLen = 0;
        uint32_t readBytesLen = 0;
        MQTTConnackFlags flags = {0};
        unsigned char connack_rc_char;
	FUNC_ENTRY;
	if(NULL == sessionPresent || NULL == connack_rc || NULL == buf) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	/* CONNACK header size is fixed at two bytes for fixed and 2 bytes for variable,
	 * using that as minimum size
	 * MQTT v3.1.1 Specification 3.2.1 */
	if(4 > buflen) {
		FUNC_EXIT_RC(MQTTPACKET_BUFFER_TOO_SHORT);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

	header.byte = readChar(&curdata);
	if(CONNACK != header.bits.type) {
		FUNC_EXIT_RC(FAILURE);
		return FAILURE;
	}

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

	flags.all = readChar(&curdata);
	*sessionPresent = flags.bits.sessionpresent;
	
	connack_rc_char = readChar(&curdata);
	switch(connack_rc_char) {
		case CONNACK_CONNECTION_ACCEPTED:
			*connack_rc = MQTT_CONNACK_CONNECTION_ACCEPTED;
			break;
		case CONANCK_UNACCEPTABLE_PROTOCOL_VERSION_ERROR:
			*connack_rc = MQTT_CONANCK_UNACCEPTABLE_PROTOCOL_VERSION_ERROR;
			break;
		case CONNACK_IDENTIFIER_REJECTED_ERROR:
			*connack_rc = MQTT_CONNACK_IDENTIFIER_REJECTED_ERROR;
			break;
		case CONNACK_SERVER_UNAVAILABLE_ERROR:
			*connack_rc = MQTT_CONNACK_SERVER_UNAVAILABLE_ERROR;
			break;
		case CONNACK_BAD_USERDATA_ERROR:
			*connack_rc = MQTT_CONNACK_BAD_USERDATA_ERROR;
			break;
		case CONNACK_NOT_AUTHORIZED_ERROR:
			*connack_rc = MQTT_CONNACK_NOT_AUTHORIZED_ERROR;
			break;
		default:
			*connack_rc = MQTT_CONNACK_UNKNOWN_ERROR;
			break;
	}

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

/**
  * Serializes a 0-length packet into the supplied buffer, ready for writing to a socket
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer, to avoid overruns
  * @param packettype the message type
  * @param serialized length
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTSerialize_zero(unsigned char *buf, size_t buflen,
								  unsigned char packetType,
								  uint32_t *serialized_length) {
        MQTTHeader header = {0};
        unsigned char *ptr = buf;
        MQTTReturnCode rc = MQTTPacket_InitHeader(&header, packetType, QOS0, 0, 0);

	FUNC_ENTRY;
	if(NULL == buf || NULL == serialized_length) {
		FUNC_EXIT_RC(MQTT_NULL_VALUE_ERROR);
		return MQTT_NULL_VALUE_ERROR;
	}

	/* Buffer should have at least 2 bytes for the header */
	if(4 > buflen) {
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
	ptr += MQTTPacket_encode(ptr, 0);
	*serialized_length = (uint32_t)(ptr - buf);

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}


/**
  * Serializes a disconnect packet into the supplied buffer, ready for writing to a socket
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer, to avoid overruns
  * @param serialized length
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTSerialize_disconnect(unsigned char *buf, size_t buflen,
										uint32_t *serialized_length) {
	return MQTTSerialize_zero(buf, buflen, DISCONNECT, serialized_length);
}


/**
  * Serializes a pingreq packet into the supplied buffer, ready for writing to a socket
  * @param buf the buffer into which the packet will be serialized
  * @param buflen the length in bytes of the supplied buffer, to avoid overruns
  * @param serialized length
  * @return MQTTReturnCode indicating function execution status
  */
MQTTReturnCode MQTTSerialize_pingreq(unsigned char *buf, size_t buflen,
									 uint32_t *serialized_length) {
	return MQTTSerialize_zero(buf, buflen, PINGREQ, serialized_length);
}
