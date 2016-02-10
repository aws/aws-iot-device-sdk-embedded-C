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

#ifndef MQTTCONNECT_H_
#define MQTTCONNECT_H_

#if !defined(DLLImport)
  #define DLLImport 
#endif
#if !defined(DLLExport)
  #define DLLExport
#endif


typedef union {
	uint8_t all;	/**< all connect flags */
#if defined(REVERSED)
	struct
	{
		unsigned int username : 1;			/**< 3.1 user name */
		unsigned int password : 1; 			/**< 3.1 password */
		unsigned int willRetain : 1;		/**< will retain setting */
		unsigned int willQoS : 2;				/**< will QoS value */
		unsigned int will : 1;			    /**< will flag */
		unsigned int cleansession : 1;	  /**< clean session flag */
		unsigned int : 1;	  	          /**< unused */
	} bits;
#else
	struct
	{
		unsigned int : 1;	     					/**< unused */
		unsigned int cleansession : 1;	  /**< cleansession flag */
		unsigned int will : 1;			    /**< will flag */
		unsigned int willQoS : 2;				/**< will QoS value */
		unsigned int willRetain : 1;		/**< will retain setting */
		unsigned int password : 1; 			/**< 3.1 password */
		unsigned int username : 1;			/**< 3.1 user name */
	} bits;
#endif
} MQTTConnectFlags;	/**< connect flags byte */



/**
 * Defines the MQTT "Last Will and Testament" (LWT) settings for
 * the connect packet.
 */
typedef struct {
	/** The eyecatcher for this structure.  must be MQTW. */
	char struct_id[4];
	/** The version number of this structure.  Must be 0 */
	uint8_t struct_version;
	/** The LWT topic to which the LWT message will be published. */
	MQTTString topicName;
	/** The LWT payload. */
	MQTTString message;
	/**
      * The retained flag for the LWT message (see MQTTAsync_message.retained).
      */
	uint8_t retained;
	/**
      * The quality of service setting for the LWT message (see
      * MQTTAsync_message.qos and @ref qos).
      */
	QoS qos;
} MQTTPacket_willOptions;


#define MQTTPacket_willOptions_initializer { {'M', 'Q', 'T', 'W'}, 0, {NULL, {0, NULL}}, {NULL, {0, NULL}}, 0, 0 }

typedef struct {
	/** The eyecatcher for this structure.  must be MQTC. */
	char struct_id[4];
	/** The version number of this structure.  Must be 0 */
	uint8_t struct_version;
	/** Version of MQTT to be used.  3 = 3.1 4 = 3.1.1
	  */
	uint8_t MQTTVersion;
	MQTTString clientID;
	uint16_t keepAliveInterval;
	uint8_t cleansession;
	uint8_t willFlag;
	MQTTPacket_willOptions will;
	MQTTString username;
	MQTTString password;
} MQTTPacket_connectData;

typedef union
{
	uint8_t all;	/**< all connack flags */
#if defined(REVERSED)
	struct
	{
		unsigned int sessionpresent : 1;    /**< session present flag */
		unsigned int : 7;	  	          /**< unused */
	} bits;
#else
	struct
	{
		unsigned int : 7;	     			/**< unused */
		unsigned int sessionpresent : 1;    /**< session present flag */
	} bits;
#endif
} MQTTConnackFlags;	/**< connack flags byte */

typedef enum {
	CONNACK_CONNECTION_ACCEPTED = 0,
	CONANCK_UNACCEPTABLE_PROTOCOL_VERSION_ERROR = 1,
	CONNACK_IDENTIFIER_REJECTED_ERROR = 2,
	CONNACK_SERVER_UNAVAILABLE_ERROR = 3,
	CONNACK_BAD_USERDATA_ERROR = 4,
	CONNACK_NOT_AUTHORIZED_ERROR = 5
}MQTTConnackReturnCodes;

#define MQTTPacket_connectData_initializer { {'M', 'Q', 'T', 'C'}, 0, 4, {NULL, {0, NULL}}, 60, 1, 0, \
		MQTTPacket_willOptions_initializer, {NULL, {0, NULL}}, {NULL, {0, NULL}} }

DLLExport MQTTReturnCode MQTTSerialize_connect(unsigned char *buf, size_t buflen,
									MQTTPacket_connectData *options,
									uint32_t *serialized_len);

DLLExport MQTTReturnCode MQTTDeserialize_connack(unsigned char *sessionPresent,
												 MQTTReturnCode *connack_rc,
												 unsigned char *buf, size_t buflen);

DLLExport MQTTReturnCode MQTTSerialize_disconnect(unsigned char *buf, size_t buflen,
								   uint32_t *serialized_length);

DLLExport MQTTReturnCode MQTTSerialize_pingreq(unsigned char *buf, size_t buflen,
											   uint32_t *serialized_length);

#endif /* MQTTCONNECT_H_ */
