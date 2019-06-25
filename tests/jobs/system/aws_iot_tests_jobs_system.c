/*
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
 * @file aws_iot_tests_jobs_system.c
 * @brief Full system tests for the AWS IoT Jobs library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* SDK initialization include. */
#include "iot_init.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Jobs include. */
#include "aws_iot_jobs.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Jobs system tests.
 */
TEST_GROUP( Jobs_System );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Jobs system tests.
 */
TEST_SETUP( Jobs_System )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Jobs system tests.
 */
TEST_TEAR_DOWN( Jobs_System )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Jobs system tests.
 */
TEST_GROUP_RUNNER( Jobs_System )
{
}

/*-----------------------------------------------------------*/
