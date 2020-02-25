/*
 * Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 * http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#ifndef _AWS_IOT_DOWNLOAD_CBOR_H_
#define _AWS_IOT_DOWNLOAD_CBOR_H_

/**
 * @brief Decode a Get Stream response message.
 */
int CBOR_Decode_GetStreamResponseMessage( const uint8_t * pucMessageBuffer,
												 size_t xMessageSize,
												 int32_t * plFileId,
												 int32_t * plBlockId,
												 int32_t * plBlockSize,
												 uint8_t * pucPayload,
												 size_t * pxPayloadSize );

/**
 * @brief Create an encoded Get Stream Request message.
 * service.
 */
int CBOR_Encode_GetStreamRequestMessage( uint8_t * pucMessageBuffer,
												size_t xMessageBufferSize,
												size_t * pxEncodedMessageSize,
												const char * pcClientToken,
												int32_t lFileId,
												int32_t lBlockSize,
												int32_t lBlockOffset,
												uint8_t * pucBlockBitmap,
												size_t xBlockBitmapSize );

#endif /* ifndef _AWS_IOT_DOWNLOAD_CBOR_H_ */
