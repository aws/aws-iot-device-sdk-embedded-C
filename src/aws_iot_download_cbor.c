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

/**
 * @file aws_download_cbor.c
 * @brief CBOR encode/decode routines for AWS IoT Over-the-Air updates.
 */

#include <stdlib.h>
#include <stdint.h>

#ifdef ENABLE_TINYCBOR
#include "cbor.h"
#include "aws_iot_download_cbor.h"
#include "aws_iot_download_cbor_internal.h"

/**
 * @brief Message field definitions, per the server specification.
 */

#define CBOR_GETSTREAMREQUEST_ITEM_COUNT    5

/**
 * @brief Decode a Get Stream response message.
 */
int CBOR_Decode_GetStreamResponseMessage( const uint8_t * pucMessageBuffer,
												 size_t xMessageSize,
												 int32_t * plFileId,
												 int32_t * plBlockId,
												 int32_t * plBlockSize,
												 uint8_t * pucPayload,
												 size_t * pxPayloadSize )
{
	CborError xCborResult = CborNoError;
	CborParser xCborParser;
	CborValue xCborValue, xCborMap;

	/* Initialize the parser. */
	xCborResult = cbor_parser_init( pucMessageBuffer,
									xMessageSize,
									0,
									&xCborParser,
									&xCborMap );


	/* Get the outer element and confirm that it's a "map," i.e., a set of
	 * CBOR key/value pairs. */
	if( CborNoError == xCborResult )
	{
		if( false == cbor_value_is_map( &xCborMap ) )
		{
			xCborResult = CborErrorIllegalType;
		}
	}

	/* Find the file ID. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_map_find_value( &xCborMap,
												 CBOR_FILEID_KEY,
												 &xCborValue );
	}

	if( CborNoError == xCborResult )
	{
		if( CborIntegerType != cbor_value_get_type( &xCborValue ) )
		{
			xCborResult = CborErrorIllegalType;
		}
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_get_int( &xCborValue,
										  ( int* )plFileId );
	}

	/* Find the block ID. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_map_find_value( &xCborMap,
												 CBOR_BLOCKID_KEY,
												 &xCborValue );
	}

	if( CborNoError == xCborResult )
	{
		if( CborIntegerType != cbor_value_get_type( &xCborValue ) )
		{
			xCborResult = CborErrorIllegalType;
		}
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_get_int( &xCborValue,
										  ( int* )plBlockId );
	}

	/* Find the block size. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_map_find_value( &xCborMap,
												 CBOR_BLOCKSIZE_KEY,
												 &xCborValue );
	}

	if( CborNoError == xCborResult )
	{
		if( CborIntegerType != cbor_value_get_type( &xCborValue ) )
		{
			xCborResult = CborErrorIllegalType;
		}
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_get_int( &xCborValue,
										  ( int* )plBlockSize );
	}

	/* Find the payload bytes. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_map_find_value( &xCborMap,
												 CBOR_BLOCKPAYLOAD_KEY,
												 &xCborValue );
	}

	if( CborNoError == xCborResult )
	{
		if( CborByteStringType != cbor_value_get_type( &xCborValue ) )
		{
			xCborResult = CborErrorIllegalType;
		}
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_calculate_string_length( &xCborValue,
														  pxPayloadSize );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_value_copy_byte_string( &xCborValue,
												   pucPayload,
												   pxPayloadSize,
												   NULL );
	}

	return CborNoError == xCborResult;
}



/**
 * @brief Create an encoded Get Stream Request message
 * service. The service allows block count or block bitmap to be requested,
 * but not both.
 */
int CBOR_Encode_GetStreamRequestMessage( uint8_t * pucMessageBuffer,
												size_t xMessageBufferSize,
												size_t * pxEncodedMessageSize,
												const char * pcClientToken,
												int32_t lFileId,
												int32_t lBlockSize,
												int32_t lBlockOffset,
												uint8_t * pucBlockBitmap,
												size_t xBlockBitmapSize )
{
	CborError xCborResult = CborNoError;
	CborEncoder xCborEncoder, xCborMapEncoder;

	/* Initialize the CBOR encoder. */
	cbor_encoder_init( &xCborEncoder,
					   pucMessageBuffer,
					   xMessageBufferSize,
					   0 );

	xCborResult = cbor_encoder_create_map( &xCborEncoder,
										   &xCborMapEncoder,
										   CBOR_GETSTREAMREQUEST_ITEM_COUNT );

	/* Encode the client token key and value. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz( &xCborMapEncoder,
												CBOR_CLIENTTOKEN_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz( &xCborMapEncoder,
												pcClientToken );
	}

	/* Encode the file ID key and value. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz( &xCborMapEncoder,
												CBOR_FILEID_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_int( &xCborMapEncoder,
									   lFileId );
	}

	/* Encode the block size key and value. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz( &xCborMapEncoder,
												CBOR_BLOCKSIZE_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_int( &xCborMapEncoder,
									   lBlockSize );
	}

	/* Encode the block offset key and value. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz( &xCborMapEncoder,
												CBOR_BLOCKOFFSET_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_int( &xCborMapEncoder,
									   lBlockOffset );
	}

	/* Encode the block bitmap key and value. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz( &xCborMapEncoder,
												CBOR_BLOCKBITMAP_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_byte_string( &xCborMapEncoder,
											   pucBlockBitmap,
											   xBlockBitmapSize );
	}

	/* Done with the encoder. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encoder_close_container_checked( &xCborEncoder,
															&xCborMapEncoder );
	}

	/* Get the encoded size. */
	if( CborNoError == xCborResult )
	{
		*pxEncodedMessageSize = cbor_encoder_get_buffer_size( &xCborEncoder,
															  pucMessageBuffer );
	}

	return CborNoError == xCborResult;
}
#else
int CBOR_Decode_GetStreamResponseMessage( const uint8_t * pucMessageBuffer,
												 size_t xMessageSize,
												 int32_t * plFileId,
												 int32_t * plBlockId,
												 int32_t * plBlockSize,
												 uint8_t * pucPayload,
												 size_t * pxPayloadSize )
{
	return 0;
}

int CBOR_Encode_GetStreamRequestMessage( uint8_t * pucMessageBuffer,
												size_t xMessageBufferSize,
												size_t * pxEncodedMessageSize,
												const char * pcClientToken,
												int32_t lFileId,
												int32_t lBlockSize,
												int32_t lBlockOffset,
												uint8_t * pucBlockBitmap,
												size_t xBlockBitmapSize )
{
	return 0;
}
#endif /* ENABLE_TINYCBOR */
