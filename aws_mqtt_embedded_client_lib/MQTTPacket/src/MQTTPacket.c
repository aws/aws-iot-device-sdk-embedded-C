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
 *    Sergio R. Caprile - non-blocking packet read functions for stream transport
 *******************************************************************************/

#include "StackTrace.h"
#include "MQTTPacket.h"

#include <string.h>

/**
 * Encodes the message length according to the MQTT algorithm
 * @param buf the buffer into which the encoded data is written
 * @param length the length to be encoded
 * @return the number of bytes written to buffer
 */
uint32_t MQTTPacket_encode(unsigned char *buf, size_t length) {
	uint32_t outLen = 0;

	FUNC_ENTRY;
	do {
		int16_t d = length % 128;
		length /= 128;
		/* if there are more digits to encode, set the top bit of this digit */
		if(length > 0) {
			d |= 0x80;
		}
		buf[outLen++] = (unsigned char)d;
	}while(length > 0);

	FUNC_EXIT_RC(outLen);
	return outLen;
}

/**
 * Decodes the message length according to the MQTT algorithm
 * @param getcharfn pointer to function to read the next character from the data source
 * @param value the decoded length returned
 * @return the number of bytes read from the socket
 */
MQTTReturnCode MQTTPacket_decode(uint32_t (*getcharfn)(unsigned char *, uint32_t), uint32_t *value, uint32_t *readBytesLen) {
	unsigned char c;
	uint32_t multiplier = 1;
	uint32_t len = 0;
	uint32_t getLen = 0;
#define MAX_NO_OF_REMAINING_LENGTH_BYTES 4

	FUNC_ENTRY;
	*value = 0;
	do {
		if(++len > MAX_NO_OF_REMAINING_LENGTH_BYTES) {
			/* bad data */
			FUNC_EXIT_RC(MQTTPACKET_READ_ERROR);
			return MQTTPACKET_READ_ERROR;
		}
		getLen = (*getcharfn)(&c, 1);
		if(1 != getLen) {
			FUNC_EXIT_RC(FAILURE);
			return FAILURE;
		}
		*value += (c & 127) * multiplier;
		multiplier *= 128;
	}while((c & 128) != 0);

	*readBytesLen = len;

	FUNC_EXIT_RC(SUCCESS);
	return SUCCESS;
}

size_t MQTTPacket_len(size_t rem_len) {
	rem_len += 1; /* header byte */

	/* now remaining_length field */
	if(rem_len < 128) {
		rem_len += 1;
	} else if (rem_len < 16384) {
		rem_len += 2;
	} else if (rem_len < 2097151) {
		rem_len += 3;
	} else {
		rem_len += 4;
	}

	return rem_len;
}

static unsigned char *bufptr;

uint32_t bufchar(unsigned char *c, uint32_t count) {
	uint32_t i;

	for(i = 0; i < count; ++i) {
		*c = *bufptr++;
	}

	return count;
}

MQTTReturnCode MQTTPacket_decodeBuf(unsigned char *buf, uint32_t *value, uint32_t *readBytesLen) {
	bufptr = buf;
	return MQTTPacket_decode(bufchar, value, readBytesLen);
}

/**
 * Calculates an integer from two bytes read from the input buffer
 * @param pptr pointer to the input buffer - incremented by the number of bytes used & returned
 * @return the integer value calculated
 */
int32_t readInt(unsigned char **pptr) {
	unsigned char *ptr = *pptr;
	int32_t len = 256*(*ptr) + (*(ptr+1));
	*pptr += 2;
	return len;
}

/**
 * Calculates an integer from two bytes read from the input buffer
 * @param pptr pointer to the input buffer - incremented by the number of bytes used & returned
 * @return the integer value calculated
 */
size_t readSizeT(unsigned char **pptr) {
	unsigned char *ptr = *pptr;
	size_t firstByte = (size_t)(*ptr);
	size_t secondByte = (size_t)(*(ptr+1));
	size_t size = 256 * firstByte + secondByte;
	*pptr += 2;
	return size;
}

/**
 * Calculates uint16 packet id from two bytes read from the input buffer
 * @param pptr pointer to the input buffer - incremented by the number of bytes used & returned
 * @return the value calculated
 */
uint16_t readPacketId(unsigned char **pptr) {
	unsigned char *ptr = *pptr;
	uint8_t firstByte = (uint8_t)(*ptr);
	uint8_t secondByte = (uint8_t)(*(ptr + 1));
	uint16_t len = (uint16_t)(secondByte + (256 * firstByte));
	*pptr += 2;
	return len;
}

/**
 * Reads one character from the input buffer.
 * @param pptr pointer to the input buffer - incremented by the number of bytes used & returned
 * @return the character read
 */
unsigned char readChar(unsigned char **pptr) {
	unsigned char c = **pptr;
	(*pptr)++;
	return c;
}

/**
 * Writes one character to an output buffer.
 * @param pptr pointer to the output buffer - incremented by the number of bytes used & returned
 * @param c the character to write
 */
void writeChar(unsigned char **pptr, unsigned char c) {
	**pptr = c;
	(*pptr)++;
}

/**
 * Writes an integer as 2 bytes to an output buffer.
 * @param pptr pointer to the output buffer - incremented by the number of bytes used & returned
 * @param anInt the integer to write
 */
void writePacketId(unsigned char** pptr, uint16_t anInt) {
	**pptr = (unsigned char)(anInt / 256);
	(*pptr)++;
	**pptr = (unsigned char)(anInt % 256);
	(*pptr)++;
}

/**
 * Writes an integer as 2 bytes to an output buffer.
 * @param pptr pointer to the output buffer - incremented by the number of bytes used & returned
 * @param anInt the integer to write
 */
void writeInt(unsigned char **pptr, int32_t anInt) {
	**pptr = (unsigned char)(anInt / 256);
	(*pptr)++;
	**pptr = (unsigned char)(anInt % 256);
	(*pptr)++;
}

/**
 * Writes size as 2 bytes to an output buffer.
 * @param pptr pointer to the output buffer - incremented by the number of bytes used & returned
 * @param anInt the integer to write
 */
void writeSizeT(unsigned char **pptr, size_t size) {
	**pptr = (unsigned char)(size / 256);
	(*pptr)++;
	**pptr = (unsigned char)(size % 256);
	(*pptr)++;
}

/**
 * Writes a "UTF" string to an output buffer.  Converts C string to length-delimited.
 * @param pptr pointer to the output buffer - incremented by the number of bytes used & returned
 * @param string the C string to write
 */
void writeCString(unsigned char **pptr, const char *string) {
	size_t len = strlen(string);
	writeSizeT(pptr, len);
	memcpy(*pptr, string, len);
	*pptr += len;
}

void writeMQTTString(unsigned char **pptr, MQTTString mqttstring) {
	if(mqttstring.lenstring.len > 0) {
		writeSizeT(pptr, mqttstring.lenstring.len);
		memcpy(*pptr, mqttstring.lenstring.data, mqttstring.lenstring.len);
		*pptr += mqttstring.lenstring.len;
	} else if (mqttstring.cstring) {
		writeCString(pptr, mqttstring.cstring);
	} else {
		writeInt(pptr, 0);
	}
}

/**
 * @param mqttstring the MQTTString structure into which the data is to be read
 * @param pptr pointer to the output buffer - incremented by the number of bytes used & returned
 * @param enddata pointer to the end of the data: do not read beyond
 * @return SUCCESS if successful, FAILURE if not
 */
MQTTReturnCode readMQTTLenString(MQTTString *mqttstring, unsigned char **pptr, unsigned char *enddata) {
	MQTTReturnCode rc = FAILURE;

	FUNC_ENTRY;
	/* the first two bytes are the length of the string */
	/* enough length to read the integer? */
	if(enddata - (*pptr) > 1) {
		mqttstring->lenstring.len = readSizeT(pptr); /* increments pptr to point past length */
		if(&(*pptr)[mqttstring->lenstring.len] <= enddata) {
			mqttstring->lenstring.data = (char*)*pptr;
			*pptr += mqttstring->lenstring.len;
			rc = SUCCESS;
		}
	}
	mqttstring->cstring = NULL;

	FUNC_EXIT_RC(rc);
	return rc;
}

/**
 * Return the length of the MQTTstring - C string if there is one, otherwise the length delimited string
 * @param mqttstring the string to return the length of
 * @return the length of the string
 */
size_t MQTTstrlen(MQTTString mqttstring) {
	size_t len = 0;

	if(mqttstring.cstring) {
		len = strlen(mqttstring.cstring);
	} else {
		len = mqttstring.lenstring.len;
	}

	return len;
}

/**
 * Compares an MQTTString to a C string
 * @param a the MQTTString to compare
 * @param bptr the C string to compare
 * @return boolean - equal or not
 */
uint8_t MQTTPacket_equals(MQTTString *a, char *bptr) {
	size_t alen = 0;
	size_t	blen = 0;
	char *aptr;
	
	if(a->cstring) {
		aptr = a->cstring;
		alen = strlen(a->cstring);
	} else {
		aptr = a->lenstring.data;
		alen = a->lenstring.len;
	}
	blen = strlen(bptr);
	
	return (alen == blen) && (strncmp(aptr, bptr, alen) == 0);
}

/**
 * Initialize the MQTTHeader structure. Used to ensure that Header bits are
 * always initialized using the proper mappings. No Endianness issues here since
 * the individual fields are all less than a byte. Also generates no warnings since
 * all fields are initialized using hex constants
 */
MQTTReturnCode MQTTPacket_InitHeader(MQTTHeader *header, MessageTypes message_type,
						   QoS qos, uint8_t dup, uint8_t retained) {
	if(NULL == header) {
		return MQTT_NULL_VALUE_ERROR;
	}

	/* Set all bits to zero */
	header->byte = 0;
	switch(message_type) {
		case UNKNOWN:
			/* Should never happen */
			return MQTT_UNKNOWN_ERROR;
		case CONNECT:
			header->bits.type = 0x01;
			break;
		case CONNACK:
			header->bits.type = 0x02;
			break;
		case PUBLISH:
			header->bits.type = 0x03;
			break;
		case PUBACK:
			header->bits.type = 0x04;
			break;
		case PUBREC:
			header->bits.type = 0x05;
			break;
		case PUBREL:
			header->bits.type = 0x06;
			break;
		case PUBCOMP:
			header->bits.type = 0x07;
			break;
		case SUBSCRIBE:
			header->bits.type = 0x08;
			break;
		case SUBACK:
			header->bits.type = 0x09;
			break;
		case UNSUBSCRIBE:
			header->bits.type = 0x0A;
			break;
		case UNSUBACK:
			header->bits.type = 0x0B;
			break;
		case PINGREQ:
			header->bits.type = 0x0C;
			break;
		case PINGRESP:
			header->bits.type = 0x0D;
			break;
		case DISCONNECT:
			header->bits.type = 0x0E;
			break;
		default:
			/* Should never happen */
			return MQTT_UNKNOWN_ERROR;
	}

	header->bits.dup = (1 == dup) ? 0x01 : 0x00;
	switch(qos) {
		case QOS0:
			header->bits.qos = 0x00;
			break;
		case QOS1:
			header->bits.qos = 0x01;
			break;
		case QOS2:
			header->bits.qos = 0x02;
			break;
		default:
			/* Using QOS0 as default */
			header->bits.qos = 0x00;
			break;
	}

	header->bits.retain = (1 == retained) ? 0x01 : 0x00;

	return SUCCESS;
}
