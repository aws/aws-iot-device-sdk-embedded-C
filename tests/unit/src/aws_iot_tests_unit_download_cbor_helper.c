/*
* Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * @file aws_iot_tests_unit_download_cbor_helper.c
 * @brief IoT Download CBOR API - Common Tests Helper
 */
#include <stdint.h>
#include <string.h>
#include <CppUTest/TestHarness_c.h>

#include "aws_iot_log.h"
#include "aws_iot_download_cbor.h"
#include "aws_iot_download_cbor_internal.h"
#include "cbor.h"

#define CBOR_TEST_MESSAGE_BUFFER_SIZE						2048
#define CBOR_TEST_SERVER_CHUNK_COUNT						8
#define CBOR_TEST_BITMAP_VALUE								0xAAAA
#define CBOR_TEST_GETSTREAMRESPONSE_MESSAGE_ITEM_COUNT		4
#define CBOR_TEST_FILEIDENTITY_VALUE						1
#define CBOR_TEST_BLOCKIDENTITY_VALUE						0
#define CBOR_TEST_FILE_ID									1
#define CBOR_TEST_BLOCK_OFFSET								0
#define CBOR_TEST_CLIENTTOKEN_VALUE							"DownloadAgentUnitTestToken"
#define CBOR_TEST_SERVER_FILES_PATH							"tests/unit/test_files/"
#define CBOR_TEST_LOG2_FILE_BLOCK_SIZE						10UL
#define CBOR_TEST_FILE_BLOCK_SIZE							( 1UL << CBOR_TEST_LOG2_FILE_BLOCK_SIZE )
#define BITS_PER_BYTE										( 1UL << LOG2_BITS_PER_BYTE )

static int prvReadCborTestFile( char * pcFileName,
								uint8_t ** ppucCborData,
								size_t * pulCborDataSize )
{
	FILE *hFile;
	int numbytes;
	int read_byte;

	hFile = fopen( pcFileName, "r" );
	if ( NULL == hFile )
		return 0;

	fseek( hFile, 0L, SEEK_END );
	numbytes = ftell( hFile );
	fseek( hFile, 0L, SEEK_SET );

	*ppucCborData = ( uint8_t * ) malloc( numbytes );
	if( NULL == *ppucCborData )
		return 0;

	*pulCborDataSize = fread( *ppucCborData, sizeof( uint8_t ), numbytes, hFile );
	fclose( hFile );

	return *pulCborDataSize == numbytes;
}

int prvCreateSampleGetStreamResponseMessage( uint8_t * pucMessageBuffer,
											 size_t xMessageBufferSize,
											 int lBlockIndex,
											 uint8_t * pucBlockPayload,
											 size_t xBlockPayloadSize,
											 size_t * pxEncodedSize )
{
	CborError xCborResult = CborNoError;
	CborEncoder xCborEncoder, xCborMapEncoder;

	/* Initialize the CBOR encoder. */
	cbor_encoder_init(
		&xCborEncoder,
		pucMessageBuffer,
		xMessageBufferSize,
		0 );
	xCborResult = cbor_encoder_create_map(
		&xCborEncoder,
		&xCborMapEncoder,
		CBOR_TEST_GETSTREAMRESPONSE_MESSAGE_ITEM_COUNT );

	/* Encode the file identity. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz(
			&xCborMapEncoder,
			CBOR_FILEID_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_int(
			&xCborMapEncoder,
			CBOR_TEST_FILEIDENTITY_VALUE );
	}

	/* Encode the block identity. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz(
			&xCborMapEncoder,
			CBOR_BLOCKID_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_int(
			&xCborMapEncoder,
			lBlockIndex );
	}

	/* Encode the block size. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz(
			&xCborMapEncoder,
			CBOR_BLOCKSIZE_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_int(
			&xCborMapEncoder,
			xBlockPayloadSize );
	}

	/* Encode the block payload. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_text_stringz(
			&xCborMapEncoder,
			CBOR_BLOCKPAYLOAD_KEY );
	}

	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encode_byte_string(
			&xCborMapEncoder,
			pucBlockPayload,
			xBlockPayloadSize );
	}

	/* Done with the encoder. */
	if( CborNoError == xCborResult )
	{
		xCborResult = cbor_encoder_close_container_checked(
			&xCborEncoder,
			&xCborMapEncoder );
	}

	/* Get the encoded size. */
	if( CborNoError == xCborResult )
	{
		*pxEncodedSize = cbor_encoder_get_buffer_size(
			&xCborEncoder,
			pucMessageBuffer );
	}

	return CborNoError == xCborResult;
}

TEST_GROUP_C_SETUP(DownloadCbor) {}

TEST_GROUP_C_TEARDOWN(DownloadCbor) {}

TEST_C(DownloadCbor, CborDownloadAgentApi) {
	int xResult = 0;
	uint8_t ucBlockPayload[ CBOR_TEST_FILE_BLOCK_SIZE ] = { 0 };
	uint8_t ucCborWork[ CBOR_TEST_MESSAGE_BUFFER_SIZE ];
	size_t xEncodedSize = 0;
	uint32_t ulBitmap = CBOR_TEST_BITMAP_VALUE;
	int lFileId = 0;
	int lFileSize = 0;
	int lBlockIndex = 0;
	int lBlockSize = 0;
	uint8_t * pucPayload = NULL;
	size_t xPayloadSize = 0;

	IOT_DEBUG( "\n-->Running Download Agent CBOR Utils Tests - CborDownloadAgentApi test \n" );

	xResult = CBOR_Encode_GetStreamRequestMessage(
		ucCborWork,
		sizeof( ucCborWork ),
		&xEncodedSize,
		CBOR_TEST_CLIENTTOKEN_VALUE,
		CBOR_TEST_FILE_ID,
		CBOR_TEST_FILE_BLOCK_SIZE,
		CBOR_TEST_BLOCK_OFFSET,
		( uint8_t * ) &ulBitmap,
		sizeof( ulBitmap ) );
	CHECK_C( xResult );

	for( int l = 0; l < sizeof( ucBlockPayload ); l++ )
	{
		ucBlockPayload[ l ] = l;
	}

	pucPayload = ( uint8_t * ) malloc( CBOR_TEST_FILE_BLOCK_SIZE );
	CHECK_C( pucPayload != NULL );

	xResult = prvCreateSampleGetStreamResponseMessage(
		ucCborWork,
		sizeof( ucCborWork ),
		CBOR_TEST_BLOCKIDENTITY_VALUE,
		ucBlockPayload,
		sizeof( ucBlockPayload ),
		&xEncodedSize );
	CHECK_C( xResult );

	xResult = CBOR_Decode_GetStreamResponseMessage(
		ucCborWork,
		xEncodedSize,
		&lFileId,
		&lBlockIndex,
		&lBlockSize,
		pucPayload,
		&xPayloadSize );
	CHECK_C( xResult );

	/* Compare the original payload and the decoded payload */
	xResult = memcmp( pucPayload, ucBlockPayload, CBOR_TEST_FILE_BLOCK_SIZE );
	CHECK_C( xResult == 0 );

	/* Compare file ID */
	CHECK_C( lFileId == CBOR_TEST_FILEIDENTITY_VALUE );

	if( NULL != pucPayload )
	{
		free( pucPayload );
		pucPayload = NULL;
	}

	IOT_DEBUG( "-->Success - CborDownloadAgentApi test \n" );
}

TEST_C(DownloadCbor, CborDownloadAgentServerFiles) {
	int xResult = 0;
	uint8_t * pucInFile = NULL;
	size_t xBufferSize = 0;
	int lFileId = 0;
	int lFileSize = 0;
	int lBlockIndex = 0;
	int lBlockSize = 0;
	uint8_t * pucPayload = NULL;
	size_t xPayloadSize = 0;
	char pcChunkFileName[ 512 ];
	uint32_t ulBitmap = CBOR_TEST_BITMAP_VALUE;

	IOT_DEBUG( "\n-->Running Download Agent CBOR Utils Tests - CborDownloadAgentServerFiles test \n" );

	for( uint32_t ulChunk = 0;
		 ulChunk < CBOR_TEST_SERVER_CHUNK_COUNT;
		 ulChunk++ )
	{
		/* Build the chunk file name. */
		snprintf( pcChunkFileName,
			sizeof( pcChunkFileName ),
			CBOR_TEST_SERVER_FILES_PATH "getStreamResponse_%d.cbor",
			ulChunk );

		/* Free the previous content buffer. */
		if( NULL != pucInFile )
		{
			free( pucInFile );
		}

		xResult = prvReadCborTestFile(
			pcChunkFileName,
			&pucInFile,
			&xBufferSize );
		CHECK_C( xResult );

		pucPayload = ( uint8_t * ) malloc( xBufferSize );
		CHECK_C( pucPayload != NULL );

		/* Parse the chunk message. */
		xResult = CBOR_Decode_GetStreamResponseMessage(
			pucInFile,
			xBufferSize,
			&lFileId,
			&lBlockIndex,
			&lBlockSize,
			pucPayload,
			&xPayloadSize );
		CHECK_C( xResult );
		CHECK_C( lFileId == CBOR_TEST_FILEIDENTITY_VALUE );
		CHECK_C( lBlockSize == xPayloadSize );

		if( NULL != pucPayload )
		{
			free( pucPayload );
			pucPayload = NULL;
		}

		/* Mark the chunk as received. */
		ulBitmap &= ~( 0x1 << lBlockIndex );
	}
	CHECK_C( ulBitmap == 0 );

	if( NULL != pucInFile )
	{
		free( pucInFile );
	}

	if( NULL != pucPayload )
	{
		free( pucPayload );
	}

	IOT_DEBUG( "-->Success - CborDownloadAgentServerFiles test \n" );
}
