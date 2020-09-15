/*
 * OTA PAL for Linux V1.0.3
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 


/* OTA PAL implementation for Windows platform. */

#include <stdio.h>
#include <stdlib.h>
#include "aws_iot_ota_pal.h"
#include "aws_iot_ota_agent_internal.h"
#include "aws_ota_codesigner_certificate.h"

#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/x509.h>
#include <openssl/pem.h>

/* Specify the OTA signature algorithm we support on this platform. */
const char cOTA_JSON_FileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

static OTA_Err_t prvPAL_CheckFileSignature( OTA_FileContext_t * const C );
static uint8_t * prvPAL_ReadAndAssumeCertificate( const uint8_t * const pucCertName,
                                                  uint32_t * const ulSignerCertSize );



/* Read the specified signer certificate from the filesystem into a local buffer. The allocated
 * memory becomes the property of the caller who is responsible for freeing it.
 */

static EVP_PKEY * Openssl_GetPkeyFromCertificate(const uint8_t * const pCertFilePath)
{
	BIO * pBio = NULL;
	X509 * pCert = NULL;
	EVP_PKEY *pPkey = NULL;
	int rc = 0;

	/* Read the cert file */
	pBio = BIO_new(BIO_s_file());
	rc = BIO_read_filename(pBio, pCertFilePath);
	if (rc != 1)
	{
		LogDebug(" TEMP solution: No cert file, get the signer cert from a pre-defined variable\n");

		/* Get the signer cert from a predefined PEM string */
		BIO_free_all(pBio);
		pBio = BIO_new(BIO_s_mem());
		BIO_puts(pBio, signingcredentialSIGNING_CERTIFICATE_PEM);
	}

	if (pBio != NULL)
	{
		if ((pCert = PEM_read_bio_X509(pBio, NULL, NULL, NULL)))
		{
			LogDebug("Getting the pkey from the X509 cert.\n");

			/* Extract the public key */
			pPkey = X509_get_pubkey(pCert);
			if (pPkey == NULL)
			{
				LogError("Error getting the pkey from signer cert.\n");
			}
		}
		else
		{
			LogError("Error loading cert from either file or predefined string.\n");
		}
	}
	else
	{
		LogError(" Failed to read signer cert.\n");
	}

	BIO_free_all(pBio);
	X509_free(pCert);

	/* pPkey should be freed by the caller */
	return pPkey;
}
/*-----------------------------------------------------------*/

static inline BaseType_t prvContextValidate( OTA_FileContext_t * C )
{
    return( ( C != NULL ) &&
            ( C->pxFile != NULL ) ); /*lint !e9034 Comparison is correct for file pointer type. */
}

/* Used to set the high bit of Windows error codes for a negative return value. */
#define OTA_PAL_INT16_NEGATIVE_MASK    ( 1 << 15 )

/* Size of buffer used in file operations on this platform (Windows). */
#define OTA_PAL_WIN_BUF_SIZE ( ( size_t ) 4096UL )

/* Attempt to create a new receive file for the file chunks as they come in. */

OTA_Err_t prvPAL_CreateFileForRx( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CreateFileForRx" );

    OTA_Err_t eResult = kOTA_Err_Uninitialized; /* For MISRA mandatory. */

    if( C != NULL )
    {
        if ( C->pucFilePath != NULL )
        {
            C->pxFile = fopen( ( const char * )C->pucFilePath, "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

            if ( C->pxFile != NULL )
            {
                eResult = kOTA_Err_None;
                OTA_LOG_L1( "[%s] Receive file created.\r\n", OTA_METHOD_NAME );
            }
            else
            {
                eResult = ( kOTA_Err_RxFileCreateFailed | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                           * Errno is being used in accordance with host API documentation.
                                                                                           * Bitmasking is being used to preserve host API error with library status code. */
                OTA_LOG_L1( "[%s] ERROR - Failed to start operation: already active!\r\n", OTA_METHOD_NAME );
            }
        }
        else
        {
            eResult = kOTA_Err_RxFileCreateFailed;
            OTA_LOG_L1( "[%s] ERROR - Invalid context provided.\r\n", OTA_METHOD_NAME );
        }
    }
    else
    {
        eResult = kOTA_Err_RxFileCreateFailed;
        OTA_LOG_L1( "[%s] ERROR - Invalid context provided.\r\n", OTA_METHOD_NAME );
    }

    return eResult; /*lint !e480 !e481 Exiting function without calling fclose.
                     * Context file handle state is managed by this API. */
}


/* Abort receiving the specified OTA update by closing the file. */

OTA_Err_t prvPAL_Abort( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_Abort" );

    /* Set default return status to uninitialized. */
    OTA_Err_t eResult = kOTA_Err_Uninitialized;
    int32_t lFileCloseResult;

    if( NULL != C )
    {
        /* Close the OTA update file if it's open. */
        if( NULL != C->pxFile )
        {
            lFileCloseResult = fclose( C->pxFile ); /*lint !e482 !e586
                                                      * Context file handle state is managed by this API. */
            C->pxFile = NULL;

            if( 0 == lFileCloseResult )
            {
                OTA_LOG_L1( "[%s] OK\r\n", OTA_METHOD_NAME );
                eResult = kOTA_Err_None;
            }
            else /* Failed to close file. */
            {
                OTA_LOG_L1( "[%s] ERROR - Closing file failed.\r\n", OTA_METHOD_NAME );
                eResult = ( kOTA_Err_FileAbort | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                  * Errno is being used in accordance with host API documentation.
                                                                                  * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            /* Nothing to do. No open file associated with this context. */
            eResult = kOTA_Err_None;
        }
    }
    else /* Context was not valid. */
    {
        OTA_LOG_L1( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME );
        eResult = kOTA_Err_FileAbort;
    }

    return eResult;
}

/* Write a block of data to the specified file. */
int16_t prvPAL_WriteBlock( OTA_FileContext_t * const C,
                           uint32_t ulOffset,
                           uint8_t * const pacData,
                           uint32_t ulBlockSize )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_WriteBlock" );

    int32_t lResult = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        lResult = fseek( C->pxFile, ulOffset, SEEK_SET ); /*lint !e586 !e713 !e9034
                                                            * C standard library call is being used for portability. */

        if( 0 == lResult )
        {
            lResult = fwrite( pacData, 1, ulBlockSize, C->pxFile ); /*lint !e586 !e713 !e9034
                                                                      * C standard library call is being used for portability. */

            if( lResult < 0 )
            {
                OTA_LOG_L1( "[%s] ERROR - fwrite failed\r\n", OTA_METHOD_NAME );
                /* Mask to return a negative value. */
                lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                                * Errno is being used in accordance with host API documentation.
                                                                * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - fseek failed\r\n", OTA_METHOD_NAME );
            /* Mask to return a negative value. */
            lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                            * Errno is being used in accordance with host API documentation.
                                                            * Bitmasking is being used to preserve host API error with library status code. */
        }
    }
    else /* Invalid context or file pointer provided. */
    {
        OTA_LOG_L1( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME );
        lResult = -1; /*TODO: Need a negative error code from the PAL here. */
    }

    return ( int16_t ) lResult;
}

/* Close the specified file. This shall authenticate the file if it is marked as secure. */

OTA_Err_t prvPAL_CloseFile( OTA_FileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CloseFile" );

    OTA_Err_t eResult = kOTA_Err_None;
    int32_t lWindowsError = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        if( C->pxSignature != NULL )
        {
            /* Verify the file signature, close the file and return the signature verification result. */
            eResult = prvPAL_CheckFileSignature( C );
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - NULL OTA Signature structure.\r\n", OTA_METHOD_NAME );
            eResult = kOTA_Err_SignatureCheckFailed;
        }

        /* Close the file. */
        lWindowsError = fclose( C->pxFile ); /*lint !e482 !e586
                                               * C standard library call is being used for portability. */
        C->pxFile = NULL;

        if( lWindowsError != 0 )
        {
            OTA_LOG_L1( "[%s] ERROR - Failed to close OTA update file.\r\n", OTA_METHOD_NAME );
            eResult = ( kOTA_Err_FileClose | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                              * Errno is being used in accordance with host API documentation.
                                                                              * Bitmasking is being used to preserve host API error with library status code. */
        }

        if( eResult == kOTA_Err_None )
        {
            OTA_LOG_L1( "[%s] %s signature verification passed.\r\n", OTA_METHOD_NAME, cOTA_JSON_FileSignatureKey );
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - Failed to pass %s signature verification: %d.\r\n", OTA_METHOD_NAME,
                        cOTA_JSON_FileSignatureKey, eResult );

			/* If we fail to verify the file signature that means the image is not valid. We need to set the image state to aborted. */
			prvPAL_SetPlatformImageState( eOTA_ImageState_Aborted );

        }
    }
    else /* Invalid OTA Context. */
    {
        /* FIXME: Invalid error code for a null file context and file handle. */
        OTA_LOG_L1( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME );
        eResult = kOTA_Err_FileClose;
    }

    return eResult;
}




/********************************************/
/* OPENSSL version
/* Verify the signature of the specified file. 
/*********************************************/

static OTA_Err_t prvPAL_CheckFileSignature( OTA_FileContext_t * const C )
{
    OTA_Err_t eResult = kOTA_Err_None;
    uint32_t bytesRead;
    uint8_t * pBuf;
    EVP_PKEY * pPkey = NULL;
    EVP_MD_CTX * pSigContext = NULL;
    int rc = 0;

    if( prvContextValidate( C ) == pdTRUE )
    {
        /* Extract the signer cert from the file */
        pPkey = Openssl_GetPkeyFromCertificate( ( const uint8_t * const ) C->pucCertFilepath );

        /* Create a new signature context for verification purpose */
        pSigContext = EVP_MD_CTX_new();

        if ( (pPkey != NULL) && (pSigContext != NULL ) )
        {   
            /* Verify an ECDSA-SHA256 signature. */
			if (1 == EVP_DigestVerifyInit(pSigContext, NULL, EVP_sha256(), NULL, pPkey))
			{
				LogDebug("[CheckFileSignature] Started signature verification, file: %s\r\n", (const char *)C->pucCertFilepath);


				pBuf = malloc(OTA_PAL_WIN_BUF_SIZE);  /* can use OPENSSL_malloc() here too */

				if (pBuf != NULL)
				{
					/* Rewind the received file to the beginning. */
					if (fseek(C->pxFile, 0L, SEEK_SET) == 0) /*lint !e586
																  * C standard library call is being used for portability. */
					{
						do
						{
							bytesRead = fread(pBuf, 1, OTA_PAL_WIN_BUF_SIZE, C->pxFile); /*lint !e586
																							   * C standard library call is being used for portability. */
																							   /* Include the file chunk in the signature validation. Zero size is OK. */
							EVP_DigestVerifyUpdate(pSigContext, pBuf, bytesRead);
						} while (bytesRead > 0UL);

						if (1 != EVP_DigestVerifyFinal(pSigContext,
							C->pxSignature->ucData,
							C->pxSignature->usSize)) /*lint !e732 !e9034 Allow comparison in this context. */
						{
							LogError("File signature check failed at FINAL\n");
							eResult = kOTA_Err_SignatureCheckFailed;
						}

					}
					else
					{
						/* Nothing special to do. */
					}

					/* Free the temporary file page buffer. This can use OPENSSL_free()*/
					free(pBuf);
				}
				else
				{
					LogError("Failed to allocate buffer memory.\n");
					eResult = kOTA_Err_OutOfMemory;
				}
			}
            else 
            {
                LogError( "File signature check failed at INIT.\n" );
                eResult = kOTA_Err_SignatureCheckFailed;
            }
        }
        else
		{
            if( pSigContext == NULL )   
			{
                LogError( "File signature check failed at NEW sig context.\n" );
                eResult = kOTA_Err_SignatureCheckFailed;
            }
            else
            {
                LogError( "File signature check failed at EXTRACT pkey from signer cert\n" );
                eResult = kOTA_Err_BadSignerCert;
            }
        }

        /* Free up objects */
        EVP_MD_CTX_free(pSigContext);
        EVP_PKEY_free(pPkey);
    }
    else
    {
        /* FIXME: Invalid error code for a NULL file context. */
        LogError( "Invalid OTA file context.\r\n" );
        /* Invalid OTA context or file pointer. */
        eResult = kOTA_Err_NullFilePtr;
    }

    return eResult;
}


/*-----------------------------------------------------------*/

OTA_Err_t prvPAL_ResetDevice( void )
{
    /* Return no error.  Windows implementation does not reset device. */
    return kOTA_Err_None;
}

/*-----------------------------------------------------------*/

OTA_Err_t prvPAL_ActivateNewImage( void )
{
    /* Return no error. Windows implementation simply does nothing on activate.
     * To run the new firmware image, double click the newly downloaded exe */
    return kOTA_Err_None;
}


/*
 * Set the final state of the last transferred (final) OTA file (or bundle).
 * On Windows, the state of the OTA image is stored in PlaformImageState.txt.
 */

OTA_Err_t prvPAL_SetPlatformImageState( OTA_ImageState_t eState )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_SetPlatformImageState" );

    OTA_Err_t eResult = kOTA_Err_None;
    FILE * pstPlatformImageState;

    if( eState != eOTA_ImageState_Unknown && eState <= eOTA_LastImageState )
    {
        pstPlatformImageState = fopen( "PlatformImageState.txt", "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

        if( pstPlatformImageState != NULL )
        {
            /* Write the image state to PlatformImageState.txt. */
            if( 1 != fwrite( &eState, sizeof( OTA_ImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                                * C standard library call is being used for portability. */
            {
                OTA_LOG_L1( "[%s] ERROR - Unable to write to image state file.\r\n", OTA_METHOD_NAME );
                eResult = ( kOTA_Err_BadImageState | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                      * Errno is being used in accordance with host API documentation.
                                                                                      * Bitmasking is being used to preserve host API error with library status code. */
            }

            /* Close PlatformImageState.txt. */
            if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586 Allow call in this context. */
            {
                OTA_LOG_L1( "[%s] ERROR - Unable to close image state file.\r\n", OTA_METHOD_NAME );
                eResult = ( kOTA_Err_BadImageState | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                      * Errno is being used in accordance with host API documentation.
                                                                                      * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] ERROR - Unable to open image state file.\r\n", OTA_METHOD_NAME );
            eResult = ( kOTA_Err_BadImageState | ( errno & kOTA_PAL_ErrMask ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                  * Errno is being used in accordance with host API documentation.
                                                                                  * Bitmasking is being used to preserve host API error with library status code. */
        }
    } /*lint !e481 Allow fopen and fclose calls in this context. */
    else /* Image state invalid. */
    {
        OTA_LOG_L1( "[%s] ERROR - Invalid image state provided.\r\n", OTA_METHOD_NAME );
        eResult = kOTA_Err_BadImageState;
    }

    return eResult; /*lint !e480 !e481 Allow calls to fopen and fclose in this context. */
}

/* Get the state of the currently running image.
 *
 * On Windows, this is simulated by looking for and reading the state from
 * the PlatformImageState.txt file in the current working directory.
 *
 * We read this at OTA_Init time so we can tell if the MCU image is in self
 * test mode. If it is, we expect a successful connection to the OTA services
 * within a reasonable amount of time. If we don't satisfy that requirement,
 * we assume there is something wrong with the firmware and reset the device,
 * causing it to rollback to the previous code. On Windows, this is not
 * fully simulated as there is no easy way to reset the simulated device.
 */
OTA_PAL_ImageState_t prvPAL_GetPlatformImageState( void )
{
    /* FIXME: This function should return OTA_PAL_ImageState_t, but it doesn't. */
    DEFINE_OTA_METHOD_NAME( "prvPAL_GetPlatformImageState" );

    FILE * pstPlatformImageState;
	OTA_ImageState_t eSavedAgentState = eOTA_ImageState_Unknown;
	OTA_PAL_ImageState_t ePalState = eOTA_PAL_ImageState_Unknown;

    pstPlatformImageState = fopen( "PlatformImageState.txt", "r+b" ); /*lint !e586
                                                                       * C standard library call is being used for portability. */

    if( pstPlatformImageState != NULL )
    {
        if( 1 != fread( &eSavedAgentState, sizeof( OTA_ImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                           * C standard library call is being used for portability. */
        {
            /* If an error occured reading the file, mark the state as aborted. */
            OTA_LOG_L1( "[%s] ERROR - Unable to read image state file.\r\n", OTA_METHOD_NAME );
			ePalState = ( eOTA_PAL_ImageState_Invalid | (errno & kOTA_PAL_ErrMask) );
        }
		else
		{
			switch (eSavedAgentState)
			{
				case eOTA_ImageState_Testing:
					ePalState = eOTA_PAL_ImageState_PendingCommit;
					break;
				case eOTA_ImageState_Accepted:
					ePalState = eOTA_PAL_ImageState_Valid;
					break;
				case eOTA_ImageState_Rejected:
				case eOTA_ImageState_Aborted:
				default:
					ePalState = eOTA_PAL_ImageState_Invalid;
					break;
			}
		}


        if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586
                                                    * C standard library call is being used for portability. */
        {
            OTA_LOG_L1( "[%s] ERROR - Unable to close image state file.\r\n", OTA_METHOD_NAME );
			ePalState = ( eOTA_PAL_ImageState_Invalid | ( errno & kOTA_PAL_ErrMask ) );
        }
    }
    else
    {
        /* If no image state file exists, assume a factory image. */
		ePalState = eOTA_PAL_ImageState_Valid; /*lint !e64 Allow assignment. */
    }

    return ePalState; /*lint !e64 !e480 !e481 I/O calls and return type are used per design. */
}

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#ifdef AMAZON_FREERTOS_ENABLE_UNIT_TESTS
#include "aws_ota_pal_test_access_define.h"
#endif
