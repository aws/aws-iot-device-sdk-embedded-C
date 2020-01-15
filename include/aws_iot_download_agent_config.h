/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/**
 * @file aws_iot_download_agent_config.h
 * @brief AWS IoT download agent configuration file
 */

#ifndef AWS_IOT_DOWNLOAD_AGENT_CONFIG_H_
#define AWS_IOT_DOWNLOAD_AGENT_CONFIG_H_

#define DLA_MAX_BLOCK_BITMAP_SIZE  128U         /* Max allowed number of bytes to track all blocks of a file. Adjust block size if more range is needed. */
#define DLA_MAX_TOPIC_LEN          256U         /* Max length of a dynamically generated topic string (usually on the stack). */

#endif /* AWS_IOT_DOWNLOAD_AGENT_H_ */
