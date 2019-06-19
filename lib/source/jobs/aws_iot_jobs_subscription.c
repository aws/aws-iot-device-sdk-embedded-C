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
 * @file aws_iot_jobs_subscription.c
 * @brief Implements functions for interacting with the Jobs library's
 * subscription list.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/*-----------------------------------------------------------*/

/**
 * @brief List of active Jobs subscriptions objects.
 */
IotListDouble_t _AwsIotJobsSubscriptions = { 0 };

/**
 * @brief Protects #_AwsIotJobsSubscriptions from concurrent access.
 */
IotMutex_t _AwsIotJobsSubscriptionsMutex;

/*-----------------------------------------------------------*/

void _AwsIotJobs_DestroySubscription( void * pData )
{
    _jobsSubscription_t * pSubscription = ( _jobsSubscription_t * ) pData;
}

/*-----------------------------------------------------------*/
