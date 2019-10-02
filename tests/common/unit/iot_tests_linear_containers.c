/*
 * IOT Common V1.1.0
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
 * @file iot_tests_linear_containers.c
 * @brief Tests for linear containers (lists and queues).
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Linear containers include. */
#include "iot_linear_containers.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Test group for linear containers tests.
 */
TEST_GROUP( Common_Unit_Linear_Containers );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for linear containers tests.
 */
TEST_SETUP( Common_Unit_Linear_Containers )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for linear containers.
 */
TEST_TEAR_DOWN( Common_Unit_Linear_Containers )
{
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for linear containers.
 */
TEST_GROUP_RUNNER( Common_Unit_Linear_Containers )
{
    RUN_TEST_CASE( Common_Unit_Linear_Containers, ListQueueEmpty );
}

/*-----------------------------------------------------------*/

TEST( Common_Unit_Linear_Containers, ListQueueEmpty )
{
    IotListDouble_t list = IOT_LIST_DOUBLE_INITIALIZER;
    IotDeQueue_t queue = IOT_DEQUEUE_INITIALIZER;

    /* Create an empty list. */
    IotListDouble_Create( &list );

    /* Check appropriate return values for an empty list. */
    TEST_ASSERT_EQUAL( 0, IotListDouble_Count( &list ) );
    TEST_ASSERT_EQUAL_INT( true, IotListDouble_IsEmpty( &list ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotListDouble_PeekHead( &list ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotListDouble_PeekTail( &list ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotListDouble_RemoveHead( &list ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotListDouble_RemoveTail( &list ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotListDouble_FindFirstMatch( &list, NULL, NULL, 0 ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotListDouble_RemoveFirstMatch( &list, NULL, NULL, 0 ) );

    /* Create an empty queue. */
    IotDeQueue_Create( &queue );

    /* Check appropriate return values for an empty queue. */
    TEST_ASSERT_EQUAL( 0, IotDeQueue_Count( &queue ) );
    TEST_ASSERT_EQUAL_INT( true, IotDeQueue_IsEmpty( &queue ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotDeQueue_PeekHead( &queue ) );
    TEST_ASSERT_EQUAL_PTR( NULL, IotDeQueue_DequeueHead( &queue ) );
}

/*-----------------------------------------------------------*/
