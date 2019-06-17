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
 * @file aws_iot.h
 * @brief Provides routines and constants that are common to AWS IoT libraries.
 * This header should not be included in typical application code.
 */

#ifndef AWS_IOT_H_
#define AWS_IOT_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>

/**
 * @brief The longest Thing Name accepted by the Shadow service, per the [AWS IoT
 * Service Limits](https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html#limits_iot).
 */
#define AWS_IOT_MAX_THING_NAME_LENGTH    ( 128 )

/**
 * @brief Checks that a Thing Name is valid for AWS IoT.
 *
 * @param[in] pThingName Thing Name to validate.
 * @param[in] thingNameLength Length of `pThingName`.
 *
 * @return `true` if `pThingName` is valid; `false` otherwise.
 */
bool AwsIot_ValidateThingName( const char * pThingName,
                               size_t thingNameLength );

#endif /* ifndef AWS_IOT_H_ */
