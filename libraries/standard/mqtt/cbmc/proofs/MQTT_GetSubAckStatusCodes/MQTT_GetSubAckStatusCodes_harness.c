/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file MQTT_GetSubAckStatusCodes_harness.c
 * @brief Implements the proof harness for MQTT_GetSubAckStatusCodes function.
 */

#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    MQTTPacketInfo_t * pSubackPacket;
    uint8_t * pPayloadStart;
    uint16_t payloadSize;

    pSubackPacket = allocateMqttPacketInfo( NULL );
    __CPROVER_assume( isValidMqttPacketInfo( pSubackPacket ) );

    MQTT_GetSubAckStatusCodes( pSubackPacket,
                               &pPayloadStart,
                               &payloadSize );
}
