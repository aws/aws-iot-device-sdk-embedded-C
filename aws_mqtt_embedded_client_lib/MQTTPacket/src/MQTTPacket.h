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
 *    Xiang Rong - 442039 Add makefile to Embedded C client
 *******************************************************************************/

#ifndef MQTTPACKET_H_
#define MQTTPACKET_H_

#if defined(__cplusplus) /* If this is a C++ compiler, use C linkage */
extern "C" {
#endif

#if defined(WIN32_DLL) || defined(WIN64_DLL)
  #define DLLImport __declspec(dllimport)
  #define DLLExport __declspec(dllexport)
#elif defined(LINUX_SO)
  #define DLLImport extern
  #define DLLExport  __attribute__ ((visibility ("default")))
#else
  #define DLLImport
  #define DLLExport  
#endif

#include "stdint.h"
#include "stddef.h"
#include "MQTTReturnCodes.h"
#include "MQTTMessage.h"

/**
 * Bitfields for the MQTT header byte.
 */
typedef union {
	unsigned char byte;	                /**< the whole byte */
#if defined(REVERSED)
	struct {
		unsigned int type : 4;			/**< message type nibble */
		unsigned int dup : 1;				/**< DUP flag bit */
		unsigned int qos : 2;				/**< QoS value, 0, 1 or 2 */
		unsigned int retain : 1;		/**< retained flag bit */
	} bits;
#else
	struct {
		unsigned int retain : 1;		/**< retained flag bit */
		unsigned int qos : 2;				/**< QoS value, 0, 1 or 2 */
		unsigned int dup : 1;				/**< DUP flag bit */
		unsigned int type : 4;			/**< message type nibble */
	} bits;
#endif
} MQTTHeader;

typedef struct {
	size_t len;
	char *data;
} MQTTLenString;

typedef struct {
	char *cstring;
	MQTTLenString lenstring;
} MQTTString;

#define MQTTString_initializer {NULL, {0, NULL}}

MQTTReturnCode MQTTPacket_InitHeader(MQTTHeader *header, MessageTypes message_type,
									 QoS qos, uint8_t dup, uint8_t retained);
size_t MQTTstrlen(MQTTString mqttstring);

#include "MQTTConnect.h"
#include "MQTTPublish.h"
#include "MQTTSubscribe.h"
#include "MQTTUnsubscribe.h"

MQTTReturnCode MQTTSerialize_ack(unsigned char *buf, size_t buflen,
								 unsigned char type, unsigned char dup, uint16_t packetid,
								 uint32_t *serialized_len);
MQTTReturnCode MQTTDeserialize_ack(unsigned char *packettype, unsigned char *dup,
								   uint16_t *packetid, unsigned char *buf,
								   size_t buflen);

size_t MQTTPacket_len(size_t rem_len);
uint8_t MQTTPacket_equals(MQTTString *a, char *bptr);

uint32_t MQTTPacket_encode(unsigned char *buf, size_t length);
MQTTReturnCode MQTTPacket_decode(uint32_t (*getcharfn)(unsigned char *, uint32_t), uint32_t *value, uint32_t *readBytesLen);
MQTTReturnCode MQTTPacket_decodeBuf(unsigned char *buf, uint32_t *value, uint32_t *readBytesLen);

uint16_t readPacketId(unsigned char **pptr);
void writePacketId(unsigned char** pptr, uint16_t anInt);

int32_t readInt(unsigned char **pptr);
size_t readSizeT(unsigned char **pptr);
unsigned char readChar(unsigned char **pptr);
void writeChar(unsigned char **pptr, unsigned char c);
void writeInt(unsigned char **pptr, int32_t anInt);
void writeSizeT(unsigned char **pptr, size_t size);
MQTTReturnCode readMQTTLenString(MQTTString *mqttstring, unsigned char **pptr, unsigned char *enddata);
void writeCString(unsigned char **pptr, const char *string);
void writeMQTTString(unsigned char **pptr, MQTTString mqttstring);

#ifdef __cplusplus /* If this is a C++ compiler, use C linkage */
}
#endif


#endif /* MQTTPACKET_H_ */
