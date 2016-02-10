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

#ifndef MQTTPUBLISH_H_
#define MQTTPUBLISH_H_

#if !defined(DLLImport)
  #define DLLImport 
#endif
#if !defined(DLLExport)
  #define DLLExport
#endif

#include "MQTTMessage.h"

DLLExport MQTTReturnCode MQTTSerialize_publish(unsigned char *buf, size_t buflen, uint8_t dup,
                                               QoS qos, uint8_t retained, uint16_t packetid,
                                               MQTTString topicName, unsigned char *payload, size_t payloadlen,
                                               uint32_t *serialized_len);

DLLExport MQTTReturnCode MQTTDeserialize_publish(unsigned char *dup, QoS *qos,
                                                 unsigned char *retained, uint16_t *packetid,
                                                 MQTTString* topicName, unsigned char **payload,
                                                 uint32_t *payloadlen, unsigned char *buf, size_t buflen);

DLLExport MQTTReturnCode MQTTSerialize_puback(unsigned char* buf, size_t buflen,
                                              uint16_t packetid, uint32_t *serialized_len);
DLLExport MQTTReturnCode MQTTSerialize_pubrel(unsigned char *buf, size_t buflen,
                                              unsigned char dup, uint16_t packetid,
                                              uint32_t *serialized_len);
DLLExport MQTTReturnCode MQTTSerialize_pubcomp(unsigned char *buf, size_t buflen,
                                               uint16_t packetid, uint32_t *serialized_len);

#endif /* MQTTPUBLISH_H_ */
