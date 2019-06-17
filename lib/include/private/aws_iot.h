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
#include <stdint.h>

/**
 * @brief The longest Thing Name accepted by AWS IoT, per the [AWS IoT
 * Service Limits](https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html#limits_iot).
 */
#define AWS_IOT_MAX_THING_NAME_LENGTH     ( 128 )

/**
 * @brief The common prefix of all AWS IoT MQTT topics.
 */
#define AWS_IOT_TOPIC_PREFIX           "$aws/things/"

/**
 * @brief The length of #AWS_IOT_TOPIC_PREFIX.
 */
#define AWS_IOT_TOPIC_PREFIX_LENGTH    ( ( uint16_t ) ( sizeof( AWS_IOT_TOPIC_PREFIX ) - 1 ) )

/**
 * @brief The suffix for an AWS IoT operation "accepted" topic.
 */
#define AWS_IOT_ACCEPTED_SUFFIX           "/accepted"

/**
 * @brief The length of #AWS_IOT_ACCEPTED_SUFFIX.
 */
#define AWS_IOT_ACCEPTED_SUFFIX_LENGTH    ( ( uint16_t ) ( sizeof( AWS_IOT_ACCEPTED_SUFFIX ) - 1 ) )

/**
 * @brief The suffix for an AWS IoT operation "rejected" topic.
 */
#define AWS_IOT_REJECTED_SUFFIX           "/rejected"

/**
 * @brief The length of #AWS_IOT_REJECTED_SUFFIX.
 */
#define AWS_IOT_REJECTED_SUFFIX_LENGTH    ( ( uint16_t ) ( sizeof( AWS_IOT_REJECTED_SUFFIX ) - 1 ) )

/**
 * @brief Enumerations representing each of the statuses that may be parsed
 * from a topic.
 */
typedef enum AwsIotStatus
{
    AWS_IOT_ACCEPTED = 0,    /**< Operation accepted. */
    AWS_IOT_REJECTED = 1,    /**< Operation rejected. */
    AWS_IOT_UNKNOWN = 2      /**< Unknown status (neither accepted nor rejected). */
} AwsIotStatus_t;

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

/**
 * @brief Parse the Thing Name from an MQTT topic.
 *
 * @param[in] pTopicName The topic to parse.
 * @param[in] topicNameLength The length of `pTopicName`.
 * @param[out] pThingName Set to point to the Thing Name.
 * @param[out] pThingNameLength Set to the length of the Thing Name.
 *
 * @return `true` if a Thing Name was successfully parsed; `false` otherwise.
 */
bool AwsIot_ParseThingName( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char ** pThingName,
                            size_t * pThingNameLength );

/**
 * @brief Parse the operation status (accepted or rejected) from an MQTT topic.
 *
 * @param[in] pTopicName The topic to parse.
 * @param[in] topicNameLength The length of `pTopicName`.
 *
 * @return Any #AwsIotStatus_t.
 */
AwsIotStatus_t AwsIot_ParseStatus( const char * pTopicName,
                                   uint16_t topicNameLength );

#endif /* ifndef AWS_IOT_H_ */
