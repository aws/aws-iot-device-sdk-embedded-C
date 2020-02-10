/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_tests_mqtt.c
 * @brief Test runner for MQTT tests.
 */

/* Standard includes. */
#include <stdbool.h>

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Runs the MQTT test groups.
 *
 * @param[in] disableNetworkTests Whether tests that require the network should run.
 * @param[in] disableLongTests Whether tests that take a long time should run.
 */
void RunMqttTests( bool disableNetworkTests, bool disableLongTests )
{
    /* Silence warnings about unused parameters. */
    ( void ) disableLongTests;

    RUN_TEST_GROUP( MQTT_Unit_Subscription );
    RUN_TEST_GROUP( MQTT_Unit_Validate );
    RUN_TEST_GROUP( MQTT_Unit_Receive );
    RUN_TEST_GROUP( MQTT_Unit_Platform );
    RUN_TEST_GROUP( MQTT_Unit_API );

    if( disableNetworkTests == false )
    {
        RUN_TEST_GROUP( MQTT_System_Platform );
        RUN_TEST_GROUP( MQTT_System );
    }
}

/*-----------------------------------------------------------*/
