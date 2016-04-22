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

#ifndef MQTTSUBSCRIBE_H_
#define MQTTSUBSCRIBE_H_

#if !defined(DLLImport)
  #define DLLImport 
#endif
#if !defined(DLLExport)
  #define DLLExport
#endif

DLLExport MQTTReturnCode MQTTSerialize_subscribe(unsigned char *buf, size_t buflen,
                                                 unsigned char dup, uint16_t packetid, uint32_t count,
                                                 MQTTString topicFilters[], QoS requestedQoSs[], 
						 uint32_t *serialized_len);

DLLExport MQTTReturnCode MQTTDeserialize_suback(uint16_t *packetid, uint32_t maxcount,
                                                uint32_t *count, QoS grantedQoSs[],
                                                unsigned char* buf, size_t buflen);


#endif /* MQTTSUBSCRIBE_H_ */
