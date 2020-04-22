/*
 * IoT MQTT V2.1.0
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file IotMqtt_Cleanup_harness.c
 * @brief Implements the proof harness for IotMqtt_Cleanup function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

void harness()
{
    /*
     * The code specification says that IotMqtt_Cleanup must be
     * called after IotMqtt_Init, since it is supposed to undo
     * anything that IotMqtt_Init does. Both IotMqtt_Cleanup and
     * IotMqtt_Init basically update the status of the same global
     * variable _initCalled. This variable is declared as volatile,
     * so CBMC will always treat it as non-deterministic.
     * Thus, even if we called IotMqtt_Init first, it does not make
     * a significant impact in this proof harness. However, since
     * the developers may change the implementation of both
     * functions in the future, we should keep both functions in the proof.
     */
    IotMqtt_Init();
    IotMqtt_Cleanup();
}
