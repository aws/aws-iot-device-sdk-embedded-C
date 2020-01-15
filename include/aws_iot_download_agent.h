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
 * @file aws_iot_download_agent.h
 * @brief Download Agent Interface
 */

/**
 * Theory of Operations and Dependencies
 *
 * AWS IoT services provided a feature for streaming contents of files
 * over the MQTT protocol, in a block by block manner. The files are
 * stored in the Simple Storage Service (S3) buckets of AWS. AWS provided
 * APIs and Command Line Interface (CLI) for creating streams in the cloud
 * and attaching files to the streams. See the README.md file under the
 * samples/linux/download_agent_sample directory for instructions.
 *
 * This library provides a simple API that can be integrated on an IoT
 * device for interacting with AWS IoT services and downloading files.
 * A device can integrate this libraryct as long as it has the capability
 * to connect to AWS IoT using the MQTT protocol.
 *
 * This library depends on a MQTT stack for interacting with AWS IoT.
 * Specifically, a device must have these three functions implemented:
 * (See aws_iot_mqtt_client_interface.h of the AWS IoT Device SDK for
 * Embedded C)
 *    aws_iot_mqtt_suscribe
 *    aws_iot_mqtt_unsubsribe
 *    aws_iot_mqtt_publish
 *
 * If a device does not incorporate the AWS IoT Device SDK for Embedded C,
 * it must provide wrapper implementations of those three functions on
 * top of the underlying MQTT stack.
 *
 * This library also depends on the CBOR protocol for encoding/decoding
 * binary payloads. See the README file under external_libs/tinycbor.
 *
 *
 */

/**
 * Programming Model
 *
 * The download agent is a library. The client of this library calls
 * aws_iot_downloand_start to kick off download sessions. Once a session
 * starts successfully, the client will receive data, block by block, in
 * a callback function - aws_iot_download_save_block. The client should
 * provide this callback function. Every time after calling
 * aws_iot_download_save_block, the download agent determines which
 * blocks have not been received, then keep requesting/receiving them
 * from AWS IoT.
 *
 * The callback function carries a parameter to indicate how many more
 * blocks remain to be downloaded. When its value becomes zero, the
 * session is complete. Then the client can invoke aws_iot_download_stop
 * to end the session. This can be done from within the
 * aws_iot_download_save_block function; or, if the client prefers, at a
 * a later time. The client can also stop a download session before it
 * completes.
 *
 * Each download session handles the downloading of one single file.
 * Each download session needs a chunk of memory for tracking its state.
 * However, this library does not use static variables, neither does it
 * allocate memory from the heap. Therefore, the client of this library
 * is responsible for allocating a chunk of memory and passing it to this
 * library's API through the pAgent parameter. The needed size of this
 * chunk can be obtained by calling a helper function -
 * aws_iot_download_agent_size. This chunk of memory shall be kept around
 * until after the client calls aws_iot_download_stop. The client should
 * not modify the content of this chunk of memory.
 *
 * There can be multiple download sessions in parallel as long as the
 * client:
 *
 * 1. Allocate a dedicated chunk of memory for each session;
 * 2. Serialize the invocation to this library's API for each individual
 *    session. (The invocations for different sessions do not have to be
 *    serialized. There is no built-in protection against re-entrance in
 *    this library.)
 *
 * This library depends on a MQTT stack. The API of this library takes
 * an opaque pointer to a chunk of memory that holds the context of the
 * MQTT stack (the pClient parameter in the API.) When this library calls
 * the underlying MQTT stack, it simply passes this opaque pointer to the
 * MQTT stack's API. If this library is used with the AWS IoT Device SDK
 * for Embedded C, this opaque pointer points to an AWS_IoT_Client
 * structure. If this library is used with another MQTT stack, this opaque
 * pointer points to whatever context data structure defined by that stack.
 * The client of this library is responsible for initializing the MQTT
 * connection and the corresponding context data structure.
 *
 */

#ifndef AWS_IOT_DOWNLOAD_AGENT_H_
#define AWS_IOT_DOWNLOAD_AGENT_H_

#include "aws_iot_mqtt_client_interface.h"

#ifdef __cplusplus
extern "C" {
#endif

#define AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS 0

/**
 * @brief Calculate how much memory is needed for each session.
 *
 * @param[in] ulThingNameLen Thing name length of this device when it
 *            was registered with AWS IoT.
 * @param[in] ulStreamNameLen Length of the stream name created in AWS
 *            IoT for streaming the file.
 * @param[in] ulFileSize Size of the file in bytes.
 * @param[in] usBlockSizeLog2 Log base 2 of the size of one data block.
 *
 * @return Size of memory needed for tracking the session, in bytes.
 */
uint32_t aws_iot_download_agent_size( uint32_t ulThingNameLen,
									  uint32_t ulStreamNameLen,
									  uint32_t ulFileSize,
									  uint16_t usBlockSizeLog2 );

/**
 * @brief Start a download session for a single file.
 *
 * @note This function subscribes to proper MQTT topics for receiving data
 *       blocks streamed from AWS IoT. It then publishes a MQTT message
 *       to AWS IoT to request the first (batch of) block(s). After
 *       calling this function with success, the client will start
 *       receiving data blocks in the aws_iot_download_save_block callback.
 *
 *       The download agent does not have static variables. It does not
 *       allocate from the heap either. For each download session,
 *       The client should allocate a dedicated chunk of memory for the
 *       download agent to keep track of the session. The client should set
 *       the chunk's initial content to all zeros. Ater that, the client
 *       does not touch it any more, but should keep it around until the
 *       session finishes. The size of the memory chunk can be obtained
 *       by calling aws_iot_download_agent_size(). The pAgent parameter of
 *       this function carries a pointer to that chunk of memory.
 *
 *       The download agent signals the finish of a session by setting the
 *       ulBlocksRemaining parameter to zero when it calls
 *       aws_iot_download_save_block(). After that, the client should call
 *       aws_iot_download_stop(), then it can free the memory chunk pointed
 *       to by pAgent.
 *
 *       For each download session, this function can be re-invoked
 *       multiple times with the same set of parameters. For instance,
 *       The client can implement a timer to check whether a session
 *       has taken too long, and if so, simply re-invoke this function
 *       with the pre-existing (same) parameters. This will result in
 *       the session to refresh from its current state. The download
 *       agent will not re-download the blocks that have been successfully
 *       delivered to aws_iot_download_save_block() before.
 *
 * @param[in] pClient Context of the MQTT client. (For instance, it points
 *            to an AWS_IoT_Client structure.) Before calling this function,
 *            the caller should have already established a MQTT
 *            connection to AWS IoT. The download agent does not interpret
 *            this context. It only passes this pointer as-is when it
 *            calls MQTT topic functions of the underlying MQTT stack (e.g.,
 *            aws_iot_mqtt_subscribe).
 * @param[in] pAgent Context for this particular session. The download
 *            agent uses this context to track progress of the session. The
 *            caller should allocate memory for this, and keep it around
 *            until the session finishes. The needed size of this context
 *            can be obtaibed by calling aws_iot_download_agent_size().
 *            Do not modify the content of this memory.
 * @param[in] ulAgentSize Size of the memory chunk pointed to by pAgent.
 *            It must be equal to or larger than the value returned by
 *            aws_iot_download_agent_size. Otherwise, this function will
 *            return an error.
 * @param[in] pucThingName Thing name of this device when it was registered
 *            with AWS IoT.
 * @param[in] pucStreamName Name of the stream created in AWS IoT for
 *            streaming the file.
 * @param[in] ulServerFileID ID number of the file attached to the stream.
 *            A stream can have multiple files attached, however, each
 *            download session corresponds to one file only.
 * @param[in] ulFileSize Size of the file in bytes.
 * @param[in] usBlockSizeLog2 Log base 2 of the size of one data block.
 * @param[in] usRequestBlock Number of blocks to request from AWS IoT
 *            for each transaction. If set to AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS,
 *            the download agent will request all blocks of the file from AWS
 *            IoT at once. If set to a value greater than zero but smaller than
 *            the total number of blocks of the file, the download agent will
 *            request usRequestBlock number of blocks only for the first request,
 *            (and also for subsequent requests.) The download agent wait until
 *            all such number of blocks are received, then request next batch of
 *            usRequestBlock number of blocks. If receiving too many blocks in
 *            one batch causes memory pressure, use a smaller number for this
 *            parameter to throttle. The caller does not need to call
 *            aws_iot_download_start again after receiving usRequestBlock number
 *            of blocks. The download agent will automatically keep repeating
 *            requesting untill all blocks of the whole file are received.
 *
 * @return SUCCESS, or error code defined by IoT_Error_t.
 */
IoT_Error_t aws_iot_download_start( void * pClient,
									void * pAgent,
									uint32_t ulAgentSize,
									uint8_t * pucThingName,
									uint8_t * pucStreamName,
									uint32_t ulServerFileID,
									uint32_t ulFileSize,
									uint16_t usBlockSizeLog2,
									uint16_t usRequestBlock );

/**
 * @brief Stop a download session.
 *
 * @note Call this function after all blocks of the file have been
 *       received, or to cancel a session before it finishes.
 *       The download agent will unsubscribe from MQTT topics for
 *       incoming data. After this function returns successfully, any
 *       blocks received for this session will be silently discarded.
 *
 * @param[in] pClient Context of the MQTT client.
 * @param[in] pAgent Context for this particular session.
 *
 * @return SUCCESS, or error code defined by IoT_Error_t.
 */
IoT_Error_t aws_iot_download_stop( void * pClient,
								   void * pAgent );

/**
 * @brief Save a block of received data at the given offset.
 *
 * @note This function should be implemented by the client of the
 *       download agent. After aws_iot_download_start returns SUCCESS,
 *       this function will be called repeatedly to save received
 *       blocks. The order of the blocks received is not deterministic,
 *       however, the download agent keeps track of which blocks have
 *       not been received, and keeps requesting the remaining blocks
 *       until all blocks of the entire file are received.
 *
 * @param[in] pucStreamName Name of the stream created in AWS IoT for
 *            streaming the file.
 * @param[in] ulServerFileID ID number of the file attached to the stream.
 * @param[in] ulOffset Offset of this block, in bytes, from the beginning
 *            of the file.
 * @param[in] pacData Pointer to the block of data.
 * @param[in] ulBlockSize Total number of bytes in this block.
 * @param[in] ulBlocksRemaining The number of blocks remaining to be
 *            received in order to finish downloading the entire file.
 *            When this value becomes zero, this block is the last one
 *            of the file, then the client can call aws_iot_download_stop.
 *
 * @return The total number of bytes successfully saved. If this function
 *         returns a value that does not equal ulBlockSize, the download
 *         agent treats it as an error. Then it will call this function
 *         later again to retry saving the same block.
 */
uint32_t aws_iot_download_save_block( uint8_t * pucStreamName,
									  uint32_t ulServerFileID,
									  uint32_t ulOffset,
									  uint8_t const * pcData,
									  uint32_t ulBlockSize,
									  uint32_t ulBlocksRemaining );

/**
 * @brief Extract a block of data from an incoming MQTT message; call
 *        aws_iot_download_save_block to save it.
 *
 * @note If the MQTT stack is the one contained in the AWS IoT Device
 *       SDK for Embedded C, there is no need for the client to use
 *       this function. In that case, the download agent will invoke
 *       this function automatically.
 *
 *       Otherwise, the client needs to implement three wrapper functions:
 *       aws_iot_mqtt_subscribe, aws_iot_mqtt_unsubscribe and
 *       aws_iot_mqtt_publish. For some implementations of such wrappers,
 *       it may not be able to register the callback function pointed
 *       to by the pApplicationHandler parameter of aws_iot_mqtt_subscribe
 *       with the underlying MQTT stack. In that case, the client may choose
 *       to invoke this function directly from its MQTT message dispatcher.
 *
 *       This function calls aws_iot_download_save_block after extracting
 *       the data from the raw MQTT message.
 *
 * @param[in] pClient Context of the MQTT client.
 * @param[in] pAgent Context for this particular session.
 * @param[in] pTopicName Name of the MQTT topic from which this message
 *            was received.
 * @param[in] usTopicNameLen Length of the topic name in bytes.
 * @param[in] pcRawMsg Pointer to the raw payload of the MQTT message.
 * @param[in] ulMsgSize Size of the raw payload in bytes.
 *
 * @return SUCCESS, or error code defined by IoT_Error_t.
 */
IoT_Error_t aws_iot_download_ingest_data_block( void * pClient,
                                                void * pAgent,
                                                char * pTopicName,
                                                uint16_t usTopicNameLen,
                                                const char * pcRawMsg,
                                                uint32_t ulMsgSize );

#ifdef __cplusplus
}
#endif

#endif /* AWS_IOT_DOWNLOAD_AGENT_H_ */
