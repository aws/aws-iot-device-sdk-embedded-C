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
 * @file aws_iot_jobs_operation.c
 * @brief Implements functions that process Jobs operations.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/*-----------------------------------------------------------*/

/**
 * @brief List of active Jobs operations awaiting a response from the Jobs
 * service.
 */
IotListDouble_t _AwsIotJobsPendingOperations = { 0 };

/**
 * @brief Protects #_AwsIotJobsPendingOperations from concurrent access.
 */
IotMutex_t _AwsIotJobsPendingOperationsMutex;

/*-----------------------------------------------------------*/

void _AwsIotJobs_DestroyOperation( void * pData )
{
    _jobsOperation_t * pOperation = ( _jobsOperation_t * ) pData;

    AwsIotJobs_Assert( pOperation != NULL );
}

/*-----------------------------------------------------------*/
