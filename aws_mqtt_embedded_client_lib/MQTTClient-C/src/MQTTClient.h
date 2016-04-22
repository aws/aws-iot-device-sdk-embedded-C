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

#ifndef __MQTT_CLIENT_C_
#define __MQTT_CLIENT_C_

/* Library Header files */
#include "stdio.h"
#include "stdint.h"
#include "stddef.h"

/* MQTT Specific header files */
#include "MQTTReturnCodes.h"
#include "MQTTMessage.h"
#include "MQTTPacket.h"

/* AWS Specific header files */
#include "aws_iot_config.h"

/* Platform specific implementation header files */
#include "network_interface.h"
#include "timer_interface.h"

#define MAX_PACKET_ID 65535
#define MAX_MESSAGE_HANDLERS AWS_IOT_MQTT_NUM_SUBSCRIBE_HANDLERS

#define MIN_RECONNECT_WAIT_INTERVAL AWS_IOT_MQTT_MIN_RECONNECT_WAIT_INTERVAL
#define MAX_RECONNECT_WAIT_INTERVAL AWS_IOT_MQTT_MAX_RECONNECT_WAIT_INTERVAL

void NewTimer(Timer *);

typedef struct Client Client;

typedef struct MessageData MessageData;

typedef void (*messageHandler)(MessageData *);
typedef void (*pApplicationHandler_t)(void);
typedef void (*disconnectHandler_t)(void);
typedef int (*networkInitHandler_t)(Network *);

struct MessageData {
    MQTTMessage *message;
    MQTTString *topicName;
    pApplicationHandler_t applicationHandler;
};

MQTTReturnCode MQTTConnect(Client *c, MQTTPacket_connectData *options);
MQTTReturnCode MQTTPublish (Client *, const char *, MQTTMessage *);
MQTTReturnCode MQTTSubscribe(Client *c, const char *topicFilter, QoS qos,
                             messageHandler messageHandler, pApplicationHandler_t applicationHandler);
MQTTReturnCode MQTTResubscribe(Client *c);
MQTTReturnCode MQTTUnsubscribe(Client *c, const char *topicFilter);
MQTTReturnCode MQTTDisconnect (Client *);
MQTTReturnCode MQTTYield (Client *, uint32_t);
MQTTReturnCode MQTTAttemptReconnect(Client *c);

uint8_t MQTTIsConnected(Client *);
uint8_t MQTTIsAutoReconnectEnabled(Client *c);

void setDefaultMessageHandler(Client *, messageHandler);
MQTTReturnCode setDisconnectHandler(Client *c, disconnectHandler_t disconnectHandler);
MQTTReturnCode setAutoReconnectEnabled(Client *c, uint8_t value);

MQTTReturnCode MQTTClient(Client *, uint32_t, unsigned char *, size_t, unsigned char *,
                          size_t, uint8_t, networkInitHandler_t, TLSConnectParams *);

uint32_t MQTTGetNetworkDisconnectedCount(Client *c);
void MQTTResetNetworkDisconnectedCount(Client *c);

struct Client {
    uint8_t isConnected;
    uint8_t wasManuallyDisconnected;
    uint8_t isPingOutstanding;
    uint8_t isAutoReconnectEnabled;

    uint16_t nextPacketId;

    uint32_t commandTimeoutMs;
    uint32_t keepAliveInterval;
    uint32_t currentReconnectWaitInterval;
    uint32_t counterNetworkDisconnected;

    size_t bufSize;
    size_t readBufSize;

    unsigned char *buf;  
    unsigned char *readbuf;

    TLSConnectParams tlsConnectParams;
    MQTTPacket_connectData options;

    Network networkStack;
    Timer pingTimer;
    Timer reconnectDelayTimer;

    struct MessageHandlers {
        const char *topicFilter;
        void (*fp) (MessageData *);
        pApplicationHandler_t applicationHandler;
        QoS qos;
    } messageHandlers[MAX_MESSAGE_HANDLERS];      /* Message handlers are indexed by subscription topic */
    
    void (* defaultMessageHandler) (MessageData *);
    disconnectHandler_t disconnectHandler;
    networkInitHandler_t networkInitHandler;
};

#define DefaultClient {0, 0, 0, 0, NULL, NULL, 0, 0, 0}

#endif
