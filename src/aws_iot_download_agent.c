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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aws_iot_log.h"

#include "aws_iot_download_agent.h"
#include "aws_iot_download_agent_config.h"

#include "aws_iot_download_cbor.h"

#define LOG2_BITS_PER_BYTE         3UL                              /* Log base 2 of bits per byte. */
#define BITS_PER_BYTE              ( 1UL << LOG2_BITS_PER_BYTE )    /* Number of bits in a byte. This is used by the block bitmap implementation. */
#define DLA_FILE_BLOCK_SIZE(_x)    ( 1UL << (_x) )                  /* Data section size of the file data block message (excludes the header). */

#define DLA_CLIENT_TOKEN           "rdy"                            /* Arbitrary client token sent in the stream "GET" message. */
#define DLA_REQUEST_MSG_MAX_SIZE   ( 3U * DLA_MAX_BLOCK_BITMAP_SIZE )

/* The starting state of a group of erased blocks in the Rx block bitmap */
#define ERASED_BLOCKS_VAL           0xffU
#define ALIGN                       ( 4UL )
#define ADDR_ALIGN(_addr)           ( uint8_t * )((uintptr_t)((uint8_t *)_addr + (ALIGN - 1)) & (-ALIGN))

static const char pcStreamData_TopicTemplate[] = "$aws/things/%s/streams/%s/data/cbor";
static const char pcGetStream_TopicTemplate[] = "$aws/things/%s/streams/%s/get/cbor";

typedef enum
{
	eDLA_AgentState_Unknown = -1,          /*!< The Download agent state is not yet known. */
	eDLA_AgentState_Uninitialized = 0,     /*!< The Download agent task is not running. */
	eDLA_AgentState_Initialized = 1,       /*!< The Download agent task is running and ready to transfer. */
	eDLA_NumAgentStates = 2
} DLA_State_t;

/**
 * @brief Download File Context Information.
 *
 * Information about a file that is to be streamed. This structure is filled in from a
 * job notification MQTT message. Currently only one file context can be streamed at time.
 */
typedef struct
{
	uint32_t ulFileSize;                              /*!< The size of the file in bytes. */
	uint32_t ulBlocksRemaining;                       /*!< How many blocks remain to be received (a code optimization). */
	uint32_t ulServerFileID;                          /*!< The file is referenced by this numeric ID in the custom job. */
	uint16_t usBlockSizeLog2;                         /*!< Log base 2 of the size of the file data block message. */
	uint16_t usRequestBlock;                          /*!< The number of blocks requested for one time. */
	uint16_t usBlockNumTrans;                         /*!< Number of blocks transfered for one time. */
	uint16_t usBitmapPos;                             /*!< The position of bitmap for bit shift. */
	uint8_t * pucStreamName;                          /*!< The stream associated with this file from the data block service. */
	uint8_t * pucRxBlockBitmap;                       /*!< Bitmap of blocks received (for de-duping and missing block request). */
	uint8_t * pucPayload;
} DLA_FileContext_t;

typedef struct download_agent_context
{
	DLA_State_t eState;                               /* State of the download agent. */
	uint32_t ulAgentContextSize;                      /* The size of the download agent packet in bytes. */
	uint8_t * pucThingName;                           /* Thing name */
	uint8_t * pucSubTopicBuf;                         /* The subscription topic of data block service */
	DLA_FileContext_t pxDLA_Files;                    /* Static array of download file structures. */
} DLA_AgentContext_t;

#ifndef DOWNLOAD_AGENT_WRITE_FLASH_SUPPORTED
uint32_t aws_iot_download_save_block( uint8_t * pucStreamName,
									  uint32_t ulServerFileID,
									  uint32_t ulOffset,
									  uint8_t const * pcData,
									  uint32_t ulBlockSize,
									  uint32_t ulBlocksRemaining )
{
	return ulBlockSize;
}
#endif

static void aws_iot_dla_cleanup( DLA_AgentContext_t * pucAgent )
{
	memset(pucAgent, 0, pucAgent->ulAgentContextSize); /* Clear the entire structure now that it is free. */
}

static IoT_Error_t aws_iot_dla_bitmap_init( DLA_FileContext_t * C )
{
	uint32_t ulIndex;
	uint32_t ulNumBlocks;              /* How many data pages are in the expected update image. */
	uint32_t ulBitmapLen;              /* Length of the file block bitmap in bytes. */
	IoT_Error_t eResult = FAILURE;

	/* Calculate how many bytes we need in our bitmap for tracking received blocks.
	 * The below calculation requires power of 2 page sizes. */

	ulNumBlocks = ( C->ulFileSize + ( DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) - 1U ) ) >> C->usBlockSizeLog2;
	ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

	if( C->pucRxBlockBitmap != NULL )
	{
		if ( C->usRequestBlock == AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS )
		{
			/* Default enable all the blocks */
			memset(C->pucRxBlockBitmap,  ( int ) ERASED_BLOCKS_VAL, ulBitmapLen);

			uint8_t ulBit = 1U << ( BITS_PER_BYTE - 1U );
			uint32_t ulNumOutOfRange = ( ulBitmapLen * BITS_PER_BYTE ) - ulNumBlocks;

			for( ulIndex = 0U; ulIndex < ulNumOutOfRange; ulIndex++ )
			{
				C->pucRxBlockBitmap[ ulBitmapLen - 1U ] &= ~ulBit;
				ulBit >>= 1U;
			}
		}
		else
		{
			memset(C->pucRxBlockBitmap, 0, ulBitmapLen);

			for( ulIndex = 0U; ulIndex < C->usRequestBlock; ulIndex++ )
			{
				C->pucRxBlockBitmap[ ulIndex/BITS_PER_BYTE ] |= 1 << (ulIndex % BITS_PER_BYTE);
			}

			C->usBitmapPos += C->usRequestBlock - 1;
		}

		C->ulBlocksRemaining = ulNumBlocks; /* Initialize our blocks remaining counter. */
		eResult = SUCCESS;
	}
	else
	{
		IOT_ERROR("Error NULL pointer of bitmap");
	}

	return eResult;
}

static IoT_Error_t aws_iot_dla_publish_get_stream_message( void *pClient,
														   DLA_AgentContext_t * pxDownloadAgent )
{
	size_t xMsgSizeFromStream;
	uint32_t ulNumBlocks, ulBitmapLen, ulTopicLen;
	IoT_Error_t eResult = FAILURE;
	char pcMsg[ DLA_REQUEST_MSG_MAX_SIZE ];
	char pcTopicBuffer[ DLA_MAX_TOPIC_LEN ];
	IoT_Publish_Message_Params paramsQOS0;
	DLA_FileContext_t  * C = &pxDownloadAgent->pxDLA_Files;

	if ( ( NULL == pClient ) || ( NULL == pxDownloadAgent ) || ( NULL == C ) )
	{
		IOT_ERROR( "NULL pointer on publish message.\r\n" );
		return eResult;
	}

	paramsQOS0.qos = QOS0;
	paramsQOS0.isRetained = 0;

	ulNumBlocks = ( C->ulFileSize + ( DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) - 1U ) ) >> C->usBlockSizeLog2;
	ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

	if ( CBOR_Encode_GetStreamRequestMessage(
					( uint8_t * ) pcMsg,
					sizeof( pcMsg ),
					&xMsgSizeFromStream,
					DLA_CLIENT_TOKEN,
					( int32_t ) C->ulServerFileID,
					( int32_t ) ( DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) & 0x7fffffffUL ), /* Mask to keep lint happy. It's still a constant. */
					0,
					( uint8_t * ) C->pucRxBlockBitmap,
					ulBitmapLen ) )
	{
		paramsQOS0.payload = (void *) pcMsg;
		paramsQOS0.payloadLen = xMsgSizeFromStream;

		ulTopicLen = ( uint32_t ) snprintf( pcTopicBuffer,
											sizeof( pcTopicBuffer ),
											pcGetStream_TopicTemplate,
											pxDownloadAgent->pucThingName,
											( const char * ) C->pucStreamName );
		if( ( ulTopicLen > 0U ) && ( ulTopicLen < sizeof( pcTopicBuffer ) ) )
		{
			eResult = aws_iot_mqtt_publish(pClient, pcTopicBuffer, ulTopicLen, &paramsQOS0);

			if( eResult != SUCCESS )
			{
				IOT_ERROR( "Publish failed: %s\r\n", pcTopicBuffer );
			}
			else
			{
				IOT_INFO( "Publish OK: %s\r\n", pcTopicBuffer );
			}
		}
		else
		{
			/* 0 should never happen since we supply the format strings. It must be overflow. */
			IOT_ERROR( "Failed to publish stream topic!\r\n" );
			aws_iot_dla_cleanup(pxDownloadAgent);
			eResult = FAILURE;
		}
	}
	else
	{
		IOT_ERROR( "CBOR encode failed.\r\n" );
		aws_iot_dla_cleanup(pxDownloadAgent);
		eResult = FAILURE;
	}

	return eResult;
}

static IoT_Error_t aws_iot_dla_subscribe_data_stream( void * pClient,
													  DLA_AgentContext_t * pxDownloadAgent,
													  const char *pTopicName,
													  uint16_t topicNameLen,
													  pApplicationHandler_t pApplicationHandler )
{
	IoT_Error_t eResult = FAILURE;

	if( ( topicNameLen > 0U ) && ( pTopicName ) )
	{
		eResult = aws_iot_mqtt_subscribe(pClient, pTopicName, topicNameLen, QOS0, pApplicationHandler, pxDownloadAgent);
		if(SUCCESS != eResult)
		{
			IOT_ERROR( "Subscribe failed: %s\n\r", pTopicName );
		}
		else
		{
			IOT_INFO( "Subscribe OK: %s\n\r", pTopicName );
		}
	}
	else
	{
		IOT_ERROR( "Failed to subscribe stream topic.\n\r" );
	}

	return eResult;
}

static IoT_Error_t aws_iot_dla_unsubscribe_data_stream( void *pClient,
													    DLA_AgentContext_t * pxDownloadAgent )
{
	IoT_Error_t eResult = FAILURE;

	if ( ( NULL == pClient ) || ( NULL == pxDownloadAgent ) )
	{
		IOT_ERROR( "Null pointer on unsubscribe stream.\r\n" );
		return eResult;
	}

	if ( strlen((char *) pxDownloadAgent->pucSubTopicBuf) > 0U )
	{
		eResult = aws_iot_mqtt_unsubscribe(pClient, (char *) pxDownloadAgent->pucSubTopicBuf, strlen((char *) pxDownloadAgent->pucSubTopicBuf));
		if(SUCCESS != eResult)
		{
			IOT_ERROR( "Unsubscribe failed: %s\n\r", pxDownloadAgent->pucSubTopicBuf );
		}
		else
		{
			IOT_INFO( "Unsubscribe OK: %s\n\r", pxDownloadAgent->pucSubTopicBuf );
			eResult = SUCCESS;
		}
	}
	else
	{
		IOT_ERROR( "Failed to unsubscribe stream topic.\n\r" );
	}

	return eResult;
}

static uint32_t aws_iot_dla_get_stream_topic_size( uint32_t ulThingNameLen,	uint32_t ulStreamNameLen )
{
	return ( strlen(pcStreamData_TopicTemplate) + ulThingNameLen + ulStreamNameLen + 1 );
}

static uint32_t aws_iot_dla_get_bitmap_size( uint32_t ulFileSize, uint16_t usBlockSizeLog2 )
{
	uint32_t ulNumBlocks;
	uint32_t ulBitmapLen;

	ulNumBlocks = ( ulFileSize + ( DLA_FILE_BLOCK_SIZE(usBlockSizeLog2) - 1U ) ) >> usBlockSizeLog2;
	ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

	return ulBitmapLen;
}

static void aws_iot_dla_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
										IoT_Publish_Message_Params *params, void *pData)
{
	IoT_Error_t eResult = FAILURE;

	eResult = aws_iot_download_ingest_data_block(pClient, pData, topicName, topicNameLen, params->payload, params->payloadLen);
}

uint32_t aws_iot_download_agent_size( uint32_t ulThingNameLen,
									  uint32_t ulStreamNameLen,
									  uint32_t ulFileSize,
									  uint16_t usBlockSizeLog2 )
{
	uint32_t ulAgentSize = 0;
	uint32_t ulContextLen = 0;
	uint32_t ulTopicLen = 0;
	uint32_t ulBitmapLen = 0;

	//Size of Block for payload decode and write to flash
	ulAgentSize += DLA_FILE_BLOCK_SIZE(usBlockSizeLog2);

	//Size of agent context struct and alignment
	ulContextLen = sizeof(DLA_AgentContext_t);
	ulAgentSize += ulContextLen + (ulContextLen & (ALIGN - 1UL));

	//Size of Thing Name and alignment
	ulThingNameLen += 1; // For end of string character
	ulAgentSize += ulThingNameLen + (ulThingNameLen & (ALIGN - 1UL));

	//Size of Stream Name and alignment
	ulStreamNameLen += 1; // For end of string character
	ulAgentSize += ulStreamNameLen + (ulStreamNameLen & (ALIGN - 1UL));

	//Size of Subscribe topic and alignment
	ulTopicLen = aws_iot_dla_get_stream_topic_size(ulThingNameLen, ulStreamNameLen);
	ulAgentSize += ulTopicLen + (ulTopicLen & (ALIGN - 1UL));

	//Size of Bitmap and alignment
	ulBitmapLen = aws_iot_dla_get_bitmap_size(ulFileSize, usBlockSizeLog2);
	ulAgentSize += ulBitmapLen + (ulBitmapLen & (ALIGN - 1UL));

	return ulAgentSize;
}

IoT_Error_t aws_iot_download_ingest_data_block( void * pClient,
												void * pAgent,
												char * pTopicName,
												uint16_t usTopicNameLen,
												const char * pcRawMsg,
												uint32_t ulMsgSize )
{
	IoT_Error_t eResult = DOWNLOAD_UNINITIALIZED;
	int lFileId = 0;
	uint32_t ulBlockIndex = 0;
	uint32_t ulBlockSize = 0;
	size_t xPayloadSize = 0;
	uint8_t pucStreamId[128] = {0};
	DLA_AgentContext_t * pxDownloadAgent = (DLA_AgentContext_t * ) pAgent;
	DLA_FileContext_t * C= &pxDownloadAgent->pxDLA_Files;

	if ( (NULL == pClient) || (NULL == pAgent) || (NULL == pTopicName) || (NULL == pcRawMsg) )
	{
		IOT_ERROR("Error NULL pointer of input arguments\n");
		return FAILURE;
	}

	if ( (usTopicNameLen <= 0) || (ulMsgSize <= 0) )
	{
		IOT_ERROR("Error topic length: %d, payload size: %d\n", usTopicNameLen, ulMsgSize);
		return FAILURE;
	}

	sscanf(pTopicName, "$aws/%*[^/]/%*[^/]/%*[^/]/%[a-zA-Z0-9_-]/", pucStreamId);

	if ( strcmp(( const char * ) pucStreamId, ( const char * ) C->pucStreamName) != 0 )
	{
		IOT_ERROR("Error topic not found steam name %s!!\n", C->pucStreamName);
		return DOWNLOAD_BAD_DATA;
	}

	/* If we have a block bitmap available then process the message. */
	if( C->pucRxBlockBitmap && ( C->ulBlocksRemaining > 0U ) )
	{
		/* Parse the chunk message. */
		if ( !CBOR_Decode_GetStreamResponseMessage(
			( const uint8_t * ) pcRawMsg,
			ulMsgSize,
			( int32_t * ) &lFileId,
			( int32_t * ) &ulBlockIndex,
			( int32_t * ) &ulBlockSize,
			C->pucPayload,
			( size_t * ) &xPayloadSize ) )
		{
			IOT_ERROR("Bad data!!\n");
			eResult = DOWNLOAD_BAD_DATA;
		}
		else
		{
			/* Validate the block index and size. */
			/* If it is NOT the last block, it MUST be equal to a full block size. */
			/* If it IS the last block, it MUST be equal to the expected remainder. */
			/* If the block ID is out of range, that's an error so abort. */
			uint32_t iLastBlock = ( ( C->ulFileSize + ( DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) - 1U ) ) >> C->usBlockSizeLog2 ) - 1U;

			if ( lFileId != C->ulServerFileID )
			{
				IOT_ERROR("File ID %d is wrong!!\n", lFileId);
				eResult = DOWNLOAD_BAD_DATA;
			}
			else if ( xPayloadSize > DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) )
			{
				IOT_ERROR("Out of memory, payload size=%zu\n", xPayloadSize);
				eResult = DOWNLOAD_UNEXPECTED_BLOCK;
			}
			else if( ( ( ( uint32_t ) ulBlockIndex < iLastBlock ) && ( ulBlockSize == DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) ) ) ||
					 ( ( ( uint32_t ) ulBlockIndex == iLastBlock ) && ( ( uint32_t ) ulBlockSize == ( C->ulFileSize - ( iLastBlock * DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) ) ) ) ) )
			{
				IOT_INFO( "Received file block %u, size %u\r\n", ulBlockIndex, ulBlockSize );

				/* Create bit mask for use in our bitmap. */
				uint8_t ulBitMask = 1U << ( ulBlockIndex % BITS_PER_BYTE ); /*lint !e9031 The composite expression will never be greater than BITS_PER_BYTE(8). */
				/* Calculate byte offset into bitmap. */
				uint32_t ulByte = ulBlockIndex >> LOG2_BITS_PER_BYTE;

				if( ( C->pucRxBlockBitmap[ ulByte ] & ulBitMask ) == 0U ) /* If we've already received this block... */
				{
					IOT_INFO( "block %u is a DUPLICATE.\r\n", ulBlockIndex);
					eResult = DOWNLOAD_DUPLICATE_CONTINUE;
				}
				else
				{
					int32_t iBytesWritten;
					uint32_t ulIndex;

					iBytesWritten = aws_iot_download_save_block( C->pucStreamName, lFileId, ( ulBlockIndex * DLA_FILE_BLOCK_SIZE(C->usBlockSizeLog2) ), C->pucPayload,  ( uint32_t ) xPayloadSize, C->ulBlocksRemaining - 1);

					if ( iBytesWritten == xPayloadSize )
					{
						C->pucRxBlockBitmap[ ulByte ] &= ~ulBitMask; /* Mark this block as received in our bitmap. */
						if ( C->usBlockNumTrans > 0)
							C->usBlockNumTrans--;
						if ( C->ulBlocksRemaining > 0)
							C->ulBlocksRemaining--;

						if (( C->usRequestBlock != AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS ) &&
							( C->usBlockNumTrans == 0 ))
						{

							if ( C->ulBlocksRemaining > C->usRequestBlock )
								C->usBlockNumTrans = C->usRequestBlock;
							else
								C->usBlockNumTrans = C->ulBlocksRemaining;

							for( ulIndex = 0U; ulIndex < C->usBlockNumTrans; ulIndex++ )
							{
								C->usBitmapPos++;

								ulBitMask = 1U << ( C->usBitmapPos % BITS_PER_BYTE );
								ulByte = C->usBitmapPos >> LOG2_BITS_PER_BYTE;

								C->pucRxBlockBitmap[ ulByte ] |= ulBitMask;
							}

							aws_iot_dla_publish_get_stream_message( pClient, pxDownloadAgent );
						}

						eResult = DOWNLOAD_ACCEPTED_CONTINUE;
					}
					else
					{
						IOT_ERROR("Error on writing file block!!\n");
						eResult = DOWNLOAD_WRITE_BLOCK_ERROR;
					}

					if( C->ulBlocksRemaining == 0U )
					{
						IOT_INFO( "Received final expected block of file.\r\n" );
						eResult = SUCCESS;
					}
					else
					{
						IOT_INFO( "Remaining: %u\r\n", C->ulBlocksRemaining );
					}
				}
			}
			else
			{
				IOT_ERROR( "Error! Block %u out of expected range! Size %u\r\n", ulBlockIndex, ulBlockSize );
				eResult = DOWNLOAD_BLOCK_OUT_OF_RANGE;
			}
		}
	}
	else
	{
		eResult = DOWNLOAD_UNEXPECTED_BLOCK;
	}

	return eResult;
}

IoT_Error_t aws_iot_download_start( void * pClient,
									void * pAgent,
									uint32_t ulAgentSize,
									uint8_t * pucThingName,
									uint8_t * pucStreamName,
									uint32_t ulServerFileID,
									uint32_t ulFileSize,
									uint16_t usBlockSizeLog2,
									uint16_t usRequestBlock )
{
	IoT_Error_t eResult = FAILURE;
	DLA_AgentContext_t * pxDownloadAgent = (DLA_AgentContext_t *) pAgent;
	DLA_FileContext_t * C = &pxDownloadAgent->pxDLA_Files;

	size_t xMsgSizeFromStream;
	uint32_t ulNumBlocks, ulBitmapLen, ulTopicLen;
	uint32_t ulTopicBufSize = 0;
	uint16_t usTopicLength = 0;

	if ( (NULL == pClient) || (NULL == pAgent) || (NULL == pucThingName) || (NULL == pucStreamName) )
	{
		IOT_ERROR("Error NULL pointer : %d ", eResult);
		return eResult;
	}

	if ( (ulServerFileID <= 0) || (ulFileSize <= 0) || (usBlockSizeLog2 <= 0) )
	{
		IOT_ERROR("Error input argument, file id: %d, file size: %d, block size:%lu", ulServerFileID, ulFileSize, DLA_FILE_BLOCK_SIZE(usBlockSizeLog2));
		return eResult;
	}

	if ( ulAgentSize < aws_iot_download_agent_size(strlen((const char *) pucThingName), strlen((const char *) pucStreamName), ulFileSize, usBlockSizeLog2) )
	{
		IOT_ERROR("Error memory size is too small, need %dbyte ", aws_iot_download_agent_size( strlen((const char *) pucThingName), strlen((const char *) pucStreamName), ulFileSize, usBlockSizeLog2) );
		return eResult;
	}

	if (pxDownloadAgent->eState != eDLA_AgentState_Initialized)
	{
		IOT_INFO("Download agent initialize");

		pxDownloadAgent->pucThingName = ADDR_ALIGN( pxDownloadAgent + sizeof(DLA_AgentContext_t) );
		strcpy( (char *) pxDownloadAgent->pucThingName, (const char *) pucThingName);

		pxDownloadAgent->ulAgentContextSize = ulAgentSize;
		C->ulServerFileID = ulServerFileID;
		C->ulFileSize = ulFileSize;
		C->usBlockSizeLog2 = usBlockSizeLog2;
		C->usRequestBlock = usRequestBlock;

		C->pucStreamName = ADDR_ALIGN( pxDownloadAgent->pucThingName + strlen((const char *) pxDownloadAgent->pucThingName) + 1 );
		strcpy( (char *) C->pucStreamName, (const char *) pucStreamName);

		pxDownloadAgent->pucSubTopicBuf = ADDR_ALIGN( C->pucStreamName + strlen((const char *) C->pucStreamName) + 1 );
		ulTopicBufSize = aws_iot_dla_get_stream_topic_size( strlen((const char *) pucThingName), strlen((const char *) pucStreamName) );
		usTopicLength = ( uint16_t ) snprintf( ( char * ) pxDownloadAgent->pucSubTopicBuf,
														  ulTopicBufSize,
														  pcStreamData_TopicTemplate,
														  pucThingName,
														  C->pucStreamName );

		eResult = aws_iot_dla_subscribe_data_stream( pClient, pxDownloadAgent, (const char *) pxDownloadAgent->pucSubTopicBuf, usTopicLength, aws_iot_dla_callback_handler );
		if(SUCCESS != eResult)
		{
			IOT_ERROR("Error subscribing data stream : %d ", eResult);
			aws_iot_dla_cleanup(pxDownloadAgent);
			return eResult;
		}

		C->pucRxBlockBitmap = ADDR_ALIGN( pxDownloadAgent->pucSubTopicBuf + usTopicLength + 1 );
		eResult = aws_iot_dla_bitmap_init(C);
		if(SUCCESS != eResult)
		{
			IOT_ERROR("Error allocate bitmap memory : %d ", eResult);
			aws_iot_dla_cleanup(pxDownloadAgent);
			return eResult;
		}

		if ( C->usRequestBlock == AWS_IOT_DOWNLOAD_REQUEST_ALL_BLOCKS )
			C->usBlockNumTrans = C->ulBlocksRemaining;
		else
			C->usBlockNumTrans = C->usRequestBlock;

		C->pucPayload = ADDR_ALIGN( C->pucRxBlockBitmap + aws_iot_dla_get_bitmap_size(ulFileSize, usBlockSizeLog2) );

		pxDownloadAgent->eState = eDLA_AgentState_Initialized;
	}

	if ((C->pucStreamName) && (strcmp((const char *) C->pucStreamName, (const char *) pucStreamName)))
	{
		IOT_ERROR("Error stream name changed : %s ", pucStreamName);
		aws_iot_dla_cleanup(pxDownloadAgent);
		return eResult;
	}

	if ((C->ulServerFileID) && (C->ulServerFileID != ulServerFileID))
	{
		IOT_ERROR("Error file ID changed : %d ", ulServerFileID);
		aws_iot_dla_cleanup(pxDownloadAgent);
		return eResult;
	}

	eResult = aws_iot_dla_publish_get_stream_message( pClient, pxDownloadAgent );

	return eResult;
}

/* Close an existing download agent context ancd free its resources. */

IoT_Error_t aws_iot_download_stop( void * pClient, void * pAgent )
{
	IoT_Error_t eResult = FAILURE;
	DLA_AgentContext_t * pxDownloadAgent = (DLA_AgentContext_t *) pAgent;
	DLA_FileContext_t * C = &pxDownloadAgent->pxDLA_Files;

	if ( (NULL == pClient) || (NULL == pAgent) )
	{
		IOT_ERROR("Error argument in stop download.");
		return FAILURE;
	}

	/* Unsubscribe from the data stream if needed. */
	eResult = aws_iot_dla_unsubscribe_data_stream( pClient, pxDownloadAgent );
	if (SUCCESS != eResult)
	{
		IOT_ERROR("Fail to unsubscribe data stream, %d.", eResult);
		return eResult;
	}

	/* Clean up download agent variable and file context. */
	aws_iot_dla_cleanup( pxDownloadAgent );

	return SUCCESS;
}
