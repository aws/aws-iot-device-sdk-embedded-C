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
 *    Allan Stockdill-Mander/Ian Craggs - initial API and implementation and/or initial documentation
 *******************************************************************************/

#include "MQTTClient.h"
#include <string.h>

static void MQTTForceDisconnect(Client *c);

void NewMessageData(MessageData *md, MQTTString *aTopicName, MQTTMessage *aMessage, pApplicationHandler_t applicationHandler) {
    md->topicName = aTopicName;
    md->message = aMessage;
    md->applicationHandler = applicationHandler;
}

uint16_t getNextPacketId(Client *c) {
    return c->nextPacketId = (uint16_t)((MAX_PACKET_ID == c->nextPacketId) ? 1 : (c->nextPacketId + 1));
}

MQTTReturnCode sendPacket(Client *c, uint32_t length, Timer *timer) {
    int32_t sentLen = 0;
    uint32_t sent = 0;

    if(NULL == c || NULL == timer) {
        return MQTT_NULL_VALUE_ERROR;
    }

    if(length >= c->bufSize) {
    	return MQTTPACKET_BUFFER_TOO_SHORT;
    }

    while(sent < length && !expired(timer)) {
        sentLen = c->networkStack.mqttwrite(&(c->networkStack), &c->buf[sent], (int)length, left_ms(timer));
        if(sentLen < 0) {
            /* there was an error writing the data */
            break;
        }
        sent = sent + (uint32_t)sentLen;
    }

    if(sent == length) {
        /* record the fact that we have successfully sent the packet */
        //countdown(&c->pingTimer, c->keepAliveInterval);
        return SUCCESS;
    }

    return FAILURE;
}

void copyMQTTConnectData(MQTTPacket_connectData *destination, MQTTPacket_connectData *source) {
    if(NULL == destination || NULL == source) {
        return;
    }
    destination->willFlag = source->willFlag;
    destination->MQTTVersion = source->MQTTVersion;
    destination->clientID.cstring = source->clientID.cstring;
    destination->username.cstring = source->username.cstring;
    destination->password.cstring = source->password.cstring;
    destination->will.topicName.cstring = source->will.topicName.cstring;
    destination->will.message.cstring = source->will.message.cstring;
    destination->will.qos = source->will.qos;
    destination->will.retained = source->will.retained;
    destination->keepAliveInterval = source->keepAliveInterval;
    destination->cleansession = source->cleansession;
}

MQTTReturnCode MQTTClient(Client *c, uint32_t commandTimeoutMs,
                          unsigned char *buf, size_t bufSize, unsigned char *readbuf,
                          size_t readBufSize, uint8_t enableAutoReconnect,
                          networkInitHandler_t networkInitHandler,
                          TLSConnectParams *tlsConnectParams) {
    uint32_t i;
    MQTTPacket_connectData default_options = MQTTPacket_connectData_initializer;

    if(NULL == c || NULL == tlsConnectParams || NULL == buf || NULL == readbuf
       || NULL == networkInitHandler) {
        return MQTT_NULL_VALUE_ERROR;
    }

    for(i = 0; i < MAX_MESSAGE_HANDLERS; ++i) {
        c->messageHandlers[i].topicFilter = NULL;
        c->messageHandlers[i].fp = NULL;
        c->messageHandlers[i].applicationHandler = NULL;
        c->messageHandlers[i].qos = 0;
    }

    c->commandTimeoutMs = commandTimeoutMs;
    c->buf = buf;
    c->bufSize = bufSize;
    c->readbuf = readbuf;
    c->readBufSize = readBufSize;
    c->isConnected = 0;
    c->isPingOutstanding = 0;
    c->wasManuallyDisconnected = 0;
    c->counterNetworkDisconnected = 0;
    c->isAutoReconnectEnabled = enableAutoReconnect;
    c->defaultMessageHandler = NULL;
    c->disconnectHandler = NULL;
    copyMQTTConnectData(&(c->options), &default_options);

    c->networkInitHandler = networkInitHandler;
    c->tlsConnectParams.DestinationPort = tlsConnectParams->DestinationPort;
    c->tlsConnectParams.pDestinationURL = tlsConnectParams->pDestinationURL;
    c->tlsConnectParams.pDeviceCertLocation = tlsConnectParams->pDeviceCertLocation;
    c->tlsConnectParams.pDevicePrivateKeyLocation = tlsConnectParams->pDevicePrivateKeyLocation;
    c->tlsConnectParams.pRootCALocation = tlsConnectParams->pRootCALocation;
    c->tlsConnectParams.timeout_ms = tlsConnectParams->timeout_ms;
    c->tlsConnectParams.ServerVerificationFlag = tlsConnectParams->ServerVerificationFlag;

    InitTimer(&(c->pingTimer));
    InitTimer(&(c->reconnectDelayTimer));

    return SUCCESS;
}

MQTTReturnCode decodePacket(Client *c, uint32_t *value, uint32_t timeout) {
    unsigned char i;
    uint32_t multiplier = 1;
    uint32_t len = 0;
    const uint32_t MAX_NO_OF_REMAINING_LENGTH_BYTES = 4;

    if(NULL == c || NULL == value) {
        return MQTT_NULL_VALUE_ERROR;
    }

    *value = 0;

    do {
        if(++len > MAX_NO_OF_REMAINING_LENGTH_BYTES) {
            /* bad data */
            return MQTTPACKET_READ_ERROR;
        }

        if((c->networkStack.mqttread(&(c->networkStack), &i, 1, (int)timeout)) != 1) {
            /* The value argument is the important value. len is just used temporarily
             * and never used by the calling function for anything else */
            return FAILURE;
        }

        *value += ((i & 127) * multiplier);
        multiplier *= 128;
    }while((i & 128) != 0);

    /* The value argument is the important value. len is just used temporarily
     * and never used by the calling function for anything else */
    return SUCCESS;
}

MQTTReturnCode readPacket(Client *c, Timer *timer, uint8_t *packet_type) {
    MQTTHeader header = {0};
    uint32_t len = 0;
    uint32_t rem_len = 0;
    uint32_t total_bytes_read = 0;
    uint32_t bytes_to_be_read = 0;
    int32_t ret_val = 0;
    MQTTReturnCode rc;

    if(NULL == c || NULL == timer) {
        return MQTT_NULL_VALUE_ERROR;
    }

    /* 1. read the header byte.  This has the packet type in it */
    if(1 != c->networkStack.mqttread(&(c->networkStack), c->readbuf, 1, left_ms(timer))) {
        /* If a network disconnect has occurred it would have been caught by keepalive already.
         * If nothing is found at this point means there was nothing to read. Not 100% correct,
         * but the only way to be sure is to pass proper error codes from the network stack
         * which the mbedtls/openssl implementations do not return */
        return MQTT_NOTHING_TO_READ;
    }

    len = 1;
    /* 2. read the remaining length.  This is variable in itself */
    rc = decodePacket(c, &rem_len, (uint32_t)left_ms(timer));
    if(SUCCESS != rc) {
        return rc;
    }

    /* if the buffer is too short then the message will be dropped silently */
	if (rem_len >= c->readBufSize) {
		bytes_to_be_read = c->readBufSize;
		do {
			ret_val = c->networkStack.mqttread(&(c->networkStack), c->readbuf, bytes_to_be_read, left_ms(timer));
			if (ret_val > 0) {
				total_bytes_read += ret_val;
				if((rem_len - total_bytes_read) >= c->readBufSize){
					bytes_to_be_read = c->readBufSize;
				}
				else{
					bytes_to_be_read = rem_len - total_bytes_read;
				}
			}
		} while (total_bytes_read < rem_len && ret_val > 0);
		return MQTTPACKET_BUFFER_TOO_SHORT;
	}

    /* put the original remaining length back into the buffer */
    len += MQTTPacket_encode(c->readbuf + 1, rem_len);

    /* 3. read the rest of the buffer using a callback to supply the rest of the data */
    if(rem_len > 0 && (c->networkStack.mqttread(&(c->networkStack), c->readbuf + len, (int)rem_len, left_ms(timer)) != (int)rem_len)) {
        return FAILURE;
    }

    header.byte = c->readbuf[0];
    *packet_type = header.bits.type;

    return SUCCESS;
}

// assume topic filter and name is in correct format
// # can only be at end
// + and # can only be next to separator
char isTopicMatched(char *topicFilter, MQTTString *topicName) {
    char *curf = NULL;
    char *curn = NULL;
    char *curn_end = NULL;

    if(NULL == topicFilter || NULL == topicName) {
        return MQTT_NULL_VALUE_ERROR;
    }

    curf = topicFilter;
    curn = topicName->lenstring.data;
    curn_end = curn + topicName->lenstring.len;

    while(*curf && (curn < curn_end)) {
        if(*curn == '/' && *curf != '/') {
            break;
        }
        if(*curf != '+' && *curf != '#' && *curf != *curn) {
            break;
        }
        if(*curf == '+') {
            /* skip until we meet the next separator, or end of string */
            char *nextpos = curn + 1;
            while(nextpos < curn_end && *nextpos != '/')
                nextpos = ++curn + 1;
        } else if(*curf == '#') {
            /* skip until end of string */
            curn = curn_end - 1;
        }

        curf++;
        curn++;
    };

    return (curn == curn_end) && (*curf == '\0');
}

MQTTReturnCode deliverMessage(Client *c, MQTTString *topicName, MQTTMessage *message) {
    uint32_t i;
    MessageData md;

    if(NULL == c || NULL == topicName || NULL == message) {
        return MQTT_NULL_VALUE_ERROR;
    }

    // we have to find the right message handler - indexed by topic
    for(i = 0; i < MAX_MESSAGE_HANDLERS; ++i) {
        if((c->messageHandlers[i].topicFilter != 0)
           && (MQTTPacket_equals(topicName, (char*)c->messageHandlers[i].topicFilter) ||
                isTopicMatched((char*)c->messageHandlers[i].topicFilter, topicName))) {
            if(c->messageHandlers[i].fp != NULL) {
                NewMessageData(&md, topicName, message, c->messageHandlers[i].applicationHandler);
                c->messageHandlers[i].fp(&md);
                return SUCCESS;
            }
        }
    }

    if(NULL != c->defaultMessageHandler) {
        NewMessageData(&md, topicName, message, NULL);
        c->defaultMessageHandler(&md);
        return SUCCESS;
    }

    /* Message handler not found for topic */
    return FAILURE;
}

MQTTReturnCode handleDisconnect(Client *c) {
    MQTTReturnCode rc;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    rc = MQTTDisconnect(c);
    if(rc != SUCCESS){
    	// If the sendPacket prevents us from sending a disconnect packet then we have to clean the stack
    	MQTTForceDisconnect(c);
    }

    if(NULL != c->disconnectHandler) {
        c->disconnectHandler();
    }

    /* Reset to 0 since this was not a manual disconnect */
    c->wasManuallyDisconnected = 0;
    return MQTT_NETWORK_DISCONNECTED_ERROR;
}

MQTTReturnCode MQTTAttemptReconnect(Client *c) {
    MQTTReturnCode rc = MQTT_ATTEMPTING_RECONNECT;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    if(1 == c->isConnected) {
        return MQTT_NETWORK_ALREADY_CONNECTED_ERROR;
    }

    /* Ignoring return code. failures expected if network is disconnected */
    rc = MQTTConnect(c, NULL);

    /* If still disconnected handle disconnect */
    if(0 == c->isConnected) {
        return MQTT_ATTEMPTING_RECONNECT;
    }

    rc = MQTTResubscribe(c);
    if(SUCCESS != rc) {
        return rc;
    }

    return MQTT_NETWORK_RECONNECTED;
}

MQTTReturnCode handleReconnect(Client *c) {
    int8_t isPhysicalLayerConnected = 1;
    MQTTReturnCode rc = MQTT_NETWORK_RECONNECTED;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    if(!expired(&(c->reconnectDelayTimer))) {
        /* Timer has not expired. Not time to attempt reconnect yet.
         * Return attempting reconnect */
        return MQTT_ATTEMPTING_RECONNECT;
    }

    if(NULL != c->networkStack.isConnected) {
        isPhysicalLayerConnected = (int8_t)c->networkStack.isConnected(&(c->networkStack));
    }

    if(isPhysicalLayerConnected) {
        rc = MQTTAttemptReconnect(c);
        if(MQTT_NETWORK_RECONNECTED == rc) {
            return MQTT_NETWORK_RECONNECTED;
        }
    }

    c->currentReconnectWaitInterval *= 2;

    if(MAX_RECONNECT_WAIT_INTERVAL < c->currentReconnectWaitInterval) {
        return MQTT_RECONNECT_TIMED_OUT;
    }
    countdown_ms(&(c->reconnectDelayTimer), c->currentReconnectWaitInterval);
    return rc;
}

MQTTReturnCode keepalive(Client *c) {
    MQTTReturnCode rc = SUCCESS;
    Timer timer;
    uint32_t serialized_len = 0;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

	if(0 == c->keepAliveInterval) {
		return SUCCESS;
	}

	if(!expired(&c->pingTimer)) {
        return SUCCESS;
    }

    if(c->isPingOutstanding) {
        return handleDisconnect(c);
    }

    /* there is no ping outstanding - send one */
    InitTimer(&timer);
    countdown_ms(&timer, c->commandTimeoutMs);
    rc = MQTTSerialize_pingreq(c->buf, c->bufSize, &serialized_len);
    if(SUCCESS != rc) {
        return rc;
    }

    /* send the ping packet */
    rc = sendPacket(c, serialized_len, &timer);
    if(SUCCESS != rc) {
    	//If sending a PING fails we can no longer determine if we are connected.  In this case we decide we are disconnected and begin reconnection attempts
        return handleDisconnect(c);
    }

    c->isPingOutstanding = 1;
    /* start a timer to wait for PINGRESP from server */
    countdown(&c->pingTimer, c->keepAliveInterval / 2);

    return SUCCESS;
}

MQTTReturnCode handlePublish(Client *c, Timer *timer) {
    MQTTString topicName;
    MQTTMessage msg;
    MQTTReturnCode rc;
    uint32_t len = 0;

    rc = MQTTDeserialize_publish((unsigned char *) &msg.dup, (QoS *) &msg.qos, (unsigned char *) &msg.retained,
                                 (uint16_t *)&msg.id, &topicName,
                                 (unsigned char **) &msg.payload, (uint32_t *) &msg.payloadlen, c->readbuf,
                                 c->readBufSize);
    if(SUCCESS != rc) {
        return rc;
    }

    rc = deliverMessage(c, &topicName, &msg);
    if(SUCCESS != rc) {
        return rc;
    }

    if(QOS0 == msg.qos) {
        /* No further processing required for QOS0 */
        return SUCCESS;
    }

    if(QOS1 == msg.qos) {
        rc = MQTTSerialize_ack(c->buf, c->bufSize, PUBACK, 0, msg.id, &len);
    } else { /* Message is not QOS0 or 1 means only option left is QOS2 */
        rc = MQTTSerialize_ack(c->buf, c->bufSize, PUBREC, 0, msg.id, &len);
    }

    if(SUCCESS != rc) {
        return rc;
    }

    rc = sendPacket(c, len, timer);
    if(SUCCESS != rc) {
        return rc;
    }

    return SUCCESS;
}

MQTTReturnCode handlePubrec(Client *c, Timer *timer) {
    uint16_t packet_id;
    unsigned char dup, type;
    MQTTReturnCode rc;
    uint32_t len;

    rc = MQTTDeserialize_ack(&type, &dup, &packet_id, c->readbuf, c->readBufSize);
    if(SUCCESS != rc) {
        return rc;
    }

    rc = MQTTSerialize_ack(c->buf, c->bufSize, PUBREL, 0, packet_id, &len);
    if(SUCCESS != rc) {
        return rc;
    }

    /* send the PUBREL packet */
    rc = sendPacket(c, len, timer);
    if(SUCCESS != rc) {
        /* there was a problem */
        return rc;
    }

    return SUCCESS;
}

MQTTReturnCode cycle(Client *c, Timer *timer, uint8_t *packet_type) {
    MQTTReturnCode rc;
    if(NULL == c || NULL == timer) {
        return MQTT_NULL_VALUE_ERROR;
    }

    /* read the socket, see what work is due */
    rc = readPacket(c, timer, packet_type);
    if(MQTT_NOTHING_TO_READ == rc) {
        /* Nothing to read, not a cycle failure */
        return SUCCESS;
    }
    if(SUCCESS != rc) {
        return rc;
    }

    switch(*packet_type) {
        case CONNACK:
        case PUBACK:
        case SUBACK:
        case UNSUBACK:
            break;
        case PUBLISH: {
            rc = handlePublish(c, timer);
            break;
        }
        case PUBREC: {
            rc = handlePubrec(c, timer);
            break;
        }
        case PUBCOMP:
            break;
        case PINGRESP: {
            c->isPingOutstanding = 0;
            countdown(&c->pingTimer, c->keepAliveInterval);
            break;
        }
        default: {
            /* Either unknown packet type or Failure occurred
             * Should not happen */
        	return MQTT_BUFFER_RX_MESSAGE_INVALID;
            break;
        }
    }

    return rc;
}

MQTTReturnCode MQTTYield(Client *c, uint32_t timeout_ms) {
    MQTTReturnCode rc = SUCCESS;
    Timer timer;
    uint8_t packet_type;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    /* Check if network was manually disconnected */
    if(0 == c->isConnected && 1 == c->wasManuallyDisconnected) {
        return MQTT_NETWORK_MANUALLY_DISCONNECTED;
    }

    /* Check if network is disconnected and auto-reconnect is not enabled */
    if(0 == c->isConnected && 0 == c->isAutoReconnectEnabled) {
        return MQTT_NETWORK_DISCONNECTED_ERROR;
    }

    InitTimer(&timer);
    countdown_ms(&timer, timeout_ms);

    while(!expired(&timer)) {
        if(0 == c->isConnected) {
            if(MAX_RECONNECT_WAIT_INTERVAL < c->currentReconnectWaitInterval) {
                rc = MQTT_RECONNECT_TIMED_OUT;
                break;
            }
            rc = handleReconnect(c);
            /* Network reconnect attempted, check if yield timer expired before
             * doing anything else */
            continue;
        }

        rc = cycle(c, &timer, &packet_type);
        if(SUCCESS != rc) {
            break;
        }

        rc = keepalive(c);
        if(MQTT_NETWORK_DISCONNECTED_ERROR == rc && 1 == c->isAutoReconnectEnabled) {
            c->currentReconnectWaitInterval = MIN_RECONNECT_WAIT_INTERVAL;
            countdown_ms(&(c->reconnectDelayTimer), c->currentReconnectWaitInterval);
            c->counterNetworkDisconnected++;
            /* Depending on timer values, it is possible that yield timer has expired
             * Set to rc to attempting reconnect to inform client that autoreconnect
             * attempt has started */
            rc = MQTT_ATTEMPTING_RECONNECT;
        } else if(SUCCESS != rc) {
            break;
        }
    }

    return rc;
}

/* only used in single-threaded mode where one command at a time is in process */
MQTTReturnCode waitfor(Client *c, uint8_t packet_type, Timer *timer) {
    MQTTReturnCode rc = FAILURE;
    uint8_t read_packet_type = 0;
    if(NULL == c || NULL == timer) {
        return MQTT_NULL_VALUE_ERROR;
    }

    do {
        if(expired(timer)) {
            /* we timed out */
            break;
        }
        rc = cycle(c, timer, &read_packet_type);
    }while(MQTT_NETWORK_DISCONNECTED_ERROR != rc  && read_packet_type != packet_type);

    if(MQTT_NETWORK_DISCONNECTED_ERROR != rc && read_packet_type != packet_type) {
        return FAILURE;
    }

    /* Something failed or we didn't receive the expected packet, return error code */
    return rc;
}

MQTTReturnCode MQTTConnect(Client *c, MQTTPacket_connectData *options) {
    Timer connect_timer;
    MQTTReturnCode connack_rc = FAILURE;
    char sessionPresent = 0;
    uint32_t len = 0;
    MQTTReturnCode rc = FAILURE;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    InitTimer(&connect_timer);
    countdown_ms(&connect_timer, c->commandTimeoutMs);

    if(c->isConnected) {
        /* Don't send connect packet again if we are already connected */
        return MQTT_NETWORK_ALREADY_CONNECTED_ERROR;
    }

    if(NULL != options) {
        /* override default options if new options were supplied */
        copyMQTTConnectData(&(c->options), options);
    }

    c->networkInitHandler(&(c->networkStack));
    rc = c->networkStack.connect(&(c->networkStack), c->tlsConnectParams);
    if(0 != rc) {
        /* TLS Connect failed, return error */
        return FAILURE;
    }

    c->keepAliveInterval = c->options.keepAliveInterval;
    rc = MQTTSerialize_connect(c->buf, c->bufSize, &(c->options), &len);
    if(SUCCESS != rc || 0 >= len) {
        return FAILURE;
    }

    /* send the connect packet */
    rc = sendPacket(c, len, &connect_timer);
    if(SUCCESS != rc) {
        return rc;
    }

    /* this will be a blocking call, wait for the CONNACK */
    rc = waitfor(c, CONNACK, &connect_timer);
    if(SUCCESS != rc) {
        return rc;
    }

    /* Received CONNACK, check the return code */
    rc = MQTTDeserialize_connack((unsigned char *)&sessionPresent, &connack_rc, c->readbuf, c->readBufSize);
    if(SUCCESS != rc) {
        return rc;
    }

    if(MQTT_CONNACK_CONNECTION_ACCEPTED != connack_rc) {
        return connack_rc;
    }

    c->isConnected = 1;
    c->wasManuallyDisconnected = 0;
    c->isPingOutstanding = 0;
    countdown(&c->pingTimer, c->keepAliveInterval);

    return SUCCESS;
}

/* Return MAX_MESSAGE_HANDLERS value if no free index is available */
uint32_t GetFreeMessageHandlerIndex(Client *c) {
    uint32_t itr;
    for(itr = 0; itr < MAX_MESSAGE_HANDLERS; itr++) {
        if(c->messageHandlers[itr].topicFilter == NULL) {
            break;
        }
    }

    return itr;
}

MQTTReturnCode MQTTSubscribe(Client *c, const char *topicFilter, QoS qos,
                  messageHandler messageHandler, pApplicationHandler_t applicationHandler) {
    MQTTReturnCode rc = FAILURE;
    Timer timer;
    uint32_t len = 0;
    uint32_t indexOfFreeMessageHandler;
    uint32_t count = 0;
    QoS grantedQoS[3] = {QOS0, QOS0, QOS0};
    uint16_t packetId;
    MQTTString topic = MQTTString_initializer;

    if(NULL == c || NULL == topicFilter
       || NULL == messageHandler || NULL == applicationHandler) {
        return MQTT_NULL_VALUE_ERROR;
    }

    if(!c->isConnected) {
        return MQTT_NETWORK_DISCONNECTED_ERROR;
    }

    topic.cstring = (char *)topicFilter;

    InitTimer(&timer);
    countdown_ms(&timer, c->commandTimeoutMs);

    rc = MQTTSerialize_subscribe(c->buf, c->bufSize, 0, getNextPacketId(c), 1, &topic, &qos, &len);
    if(SUCCESS != rc) {
        return rc;
    }

    indexOfFreeMessageHandler = GetFreeMessageHandlerIndex(c);
    if(MAX_MESSAGE_HANDLERS <= indexOfFreeMessageHandler) {
        return MQTT_MAX_SUBSCRIPTIONS_REACHED_ERROR;
    }

    /* send the subscribe packet */
    rc = sendPacket(c, len, &timer);
    if(SUCCESS != rc) {
        return rc;
    }

    /* wait for suback */
    rc = waitfor(c, SUBACK, &timer);
    if(SUCCESS != rc) {
        return rc;
    }

    /* Granted QoS can be 0, 1 or 2 */
    rc = MQTTDeserialize_suback(&packetId, 1, &count, grantedQoS, c->readbuf, c->readBufSize);
    if(SUCCESS != rc) {
        return rc;
    }

    c->messageHandlers[indexOfFreeMessageHandler].topicFilter =
            topicFilter;
    c->messageHandlers[indexOfFreeMessageHandler].fp = messageHandler;
    c->messageHandlers[indexOfFreeMessageHandler].applicationHandler =
            applicationHandler;
    c->messageHandlers[indexOfFreeMessageHandler].qos = qos;

    return SUCCESS;
}

MQTTReturnCode MQTTResubscribe(Client *c) {
    MQTTReturnCode rc = FAILURE;
    Timer timer;
    uint32_t len = 0;
    uint32_t count = 0;
    QoS grantedQoS[3] = {QOS0, QOS0, QOS0};
    uint16_t packetId;
    uint32_t existingSubCount = 0;
    uint32_t itr = 0;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    if(!c->isConnected) {
        return MQTT_NETWORK_DISCONNECTED_ERROR;
    }

    existingSubCount = GetFreeMessageHandlerIndex(c);

    for(itr = 0; itr < existingSubCount; itr++) {
        MQTTString topic = MQTTString_initializer;
        topic.cstring = (char *)c->messageHandlers[itr].topicFilter;

        InitTimer(&timer);
        countdown_ms(&timer, c->commandTimeoutMs);

        rc = MQTTSerialize_subscribe(c->buf, c->bufSize, 0, getNextPacketId(c), 1,
                                     &topic, &(c->messageHandlers[itr].qos), &len);
        if(SUCCESS != rc) {
            return rc;
        }

        /* send the subscribe packet */
        rc = sendPacket(c, len, &timer);
        if(SUCCESS != rc) {
            return rc;
        }

        /* wait for suback */
        rc = waitfor(c, SUBACK, &timer);
        if(SUCCESS != rc) {
            return rc;
        }

        /* Granted QoS can be 0, 1 or 2 */
        rc = MQTTDeserialize_suback(&packetId, 1, &count, grantedQoS, c->readbuf, c->readBufSize);
        if(SUCCESS != rc) {
            return rc;
        }
    }

    return SUCCESS;
}

MQTTReturnCode MQTTUnsubscribe(Client *c, const char *topicFilter) {
    MQTTReturnCode rc = FAILURE;
    Timer timer;
    MQTTString topic = MQTTString_initializer;
    uint32_t len = 0;
    uint32_t i = 0;
    uint16_t packet_id;

    if(NULL == c || NULL == topicFilter) {
        return MQTT_NULL_VALUE_ERROR;
    }

    topic.cstring = (char *)topicFilter;

    if(!c->isConnected) {
        return MQTT_NETWORK_DISCONNECTED_ERROR;
    }

    InitTimer(&timer);
    countdown_ms(&timer, c->commandTimeoutMs);

    rc = MQTTSerialize_unsubscribe(c->buf, c->bufSize, 0, getNextPacketId(c), 1, &topic, &len);
    if(SUCCESS != rc) {
        return rc;
    }

    /* send the unsubscribe packet */
    rc = sendPacket(c, len, &timer);
    if(SUCCESS != rc) {
        return rc;
    }

    rc = waitfor(c, UNSUBACK, &timer);
    if(SUCCESS != rc) {
        return rc;
    }

    rc = MQTTDeserialize_unsuback(&packet_id, c->readbuf, c->readBufSize);
    if(SUCCESS != rc) {
        return rc;
    }

    /* Remove from message handler array */
    for(i = 0; i < MAX_MESSAGE_HANDLERS; ++i) {
        if(c->messageHandlers[i].topicFilter != NULL &&
            (strcmp(c->messageHandlers[i].topicFilter, topicFilter) == 0)) {
            c->messageHandlers[i].topicFilter = NULL;
            /* We don't want to break here, if the same topic is registered
             * with 2 callbacks. Unlikely scenario */
        }
    }

    return SUCCESS;
}

MQTTReturnCode MQTTPublish(Client *c, const char *topicName, MQTTMessage *message) {
    Timer timer;
    MQTTString topic = MQTTString_initializer;
    uint32_t len = 0;
    uint8_t waitForAck = 0;
    uint8_t packetType = PUBACK;
    uint16_t packet_id;
    unsigned char dup, type;
    MQTTReturnCode rc = FAILURE;

    if(NULL == c || NULL == topicName || NULL == message) {
        return MQTT_NULL_VALUE_ERROR;
    }

    topic.cstring = (char *)topicName;

    if(!c->isConnected) {
        return MQTT_NETWORK_DISCONNECTED_ERROR;
    }

    InitTimer(&timer);
    countdown_ms(&timer, c->commandTimeoutMs);

    if(QOS1 == message->qos || QOS2 == message->qos) {
        message->id = getNextPacketId(c);
        waitForAck = 1;
        if(QOS2 == message->qos) {
            packetType = PUBCOMP;
        }
    }

    rc = MQTTSerialize_publish(c->buf, c->bufSize, 0, message->qos, message->retained, message->id,
              topic, (unsigned char*)message->payload, message->payloadlen, &len);
    if(SUCCESS != rc) {
        return rc;
    }

    /* send the publish packet */
    rc = sendPacket(c, len, &timer);
    if(SUCCESS != rc) {
        return rc;
    }

    /* Wait for ack if QoS1 or QoS2 */
    if(1 == waitForAck) {
        rc = waitfor(c, packetType, &timer);
        if(SUCCESS != rc) {
            return rc;
        }

        rc = MQTTDeserialize_ack(&type, &dup, &packet_id, c->readbuf, c->readBufSize);
        if(SUCCESS != rc) {
            return rc;
        }
    }

    return SUCCESS;
}
/**
 * This is for the case when the sendPacket Fails.
 */
static void MQTTForceDisconnect(Client *c){
	c->isConnected = 0;
	c->networkStack.disconnect(&(c->networkStack));
	c->networkStack.destroy(&(c->networkStack));
}

MQTTReturnCode MQTTDisconnect(Client *c) {
    MQTTReturnCode rc = FAILURE;
    /* We might wait for incomplete incoming publishes to complete */
    Timer timer;
    uint32_t serialized_len = 0;

    if(NULL == c) {
        return MQTT_NULL_VALUE_ERROR;
    }

    if(0 == c->isConnected) {
        /* Network is already disconnected. Do nothing */
        return MQTT_NETWORK_DISCONNECTED_ERROR;
    }

    rc = MQTTSerialize_disconnect(c->buf, c->bufSize, &serialized_len);
    if(SUCCESS != rc) {
        return rc;
    }

    InitTimer(&timer);
    countdown_ms(&timer, c->commandTimeoutMs);

    /* send the disconnect packet */
    if(serialized_len > 0) {
        rc = sendPacket(c, serialized_len, &timer);
        if(SUCCESS != rc) {
            return rc;
        }
    }

    /* Clean network stack */
    c->networkStack.disconnect(&(c->networkStack));
    rc = c->networkStack.destroy(&(c->networkStack));
    if(0 != rc) {
        /* TLS Destroy failed, return error */
        return FAILURE;
    }

    c->isConnected = 0;

    /* Always set to 1 whenever disconnect is called. Keepalive resets to 0 */
    c->wasManuallyDisconnected = 1;

    return SUCCESS;
}

uint8_t MQTTIsConnected(Client *c) {
    if(NULL == c) {
        return 0;
    }

    return c->isConnected;
}

uint8_t MQTTIsAutoReconnectEnabled(Client *c) {
    if(NULL == c) {
        return 0;
    }

    return c->isAutoReconnectEnabled;
}

MQTTReturnCode setDisconnectHandler(Client *c, disconnectHandler_t disconnectHandler) {
    if(NULL == c || NULL == disconnectHandler) {
        return MQTT_NULL_VALUE_ERROR;
    }

    c->disconnectHandler = disconnectHandler;
    return SUCCESS;
}

MQTTReturnCode setAutoReconnectEnabled(Client *c, uint8_t value) {
    if(NULL == c) {
        return FAILURE;
    }
    c->isAutoReconnectEnabled = value;
    return SUCCESS;
}

uint32_t MQTTGetNetworkDisconnectedCount(Client *c) {
    return c->counterNetworkDisconnected;
}

void MQTTResetNetworkDisconnectedCount(Client *c) {
    c->counterNetworkDisconnected = 0;
}
