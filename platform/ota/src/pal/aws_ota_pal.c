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
#include <errno.h>
#include "ota_platform_interface.h"
#include "ota_private.h"
#include "aws_ota_codesigner_certificate.h"

#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/x509.h>
#include <openssl/pem.h>

/* Specify the OTA signature algorithm we support on this platform. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

static OtaErr_t prvPAL_CheckFileSignature( OtaFileContext_t * const C );
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
		LogDebug((" TEMP solution: No cert file, get the signer cert from a pre-defined variable\n"));

		/* Get the signer cert from a predefined PEM string */
		BIO_free_all(pBio);
		pBio = BIO_new(BIO_s_mem());
		BIO_puts(pBio, signingcredentialSIGNING_CERTIFICATE_PEM);
	}

	if (pBio != NULL)
	{
		if ((pCert = PEM_read_bio_X509(pBio, NULL, NULL, NULL)))
		{
			LogDebug(("Getting the pkey from the X509 cert.\n"));

			/* Extract the public key */
			pPkey = X509_get_pubkey(pCert);
			if (pPkey == NULL)
			{
				LogError(("Error getting the pkey from signer cert.\n"));
			}
		}
		else
		{
			LogError(("Error loading cert from either file or predefined string.\n"));
		}
	}
	else
	{
		LogError((" Failed to read signer cert.\n"));
	}

	BIO_free_all(pBio);
	X509_free(pCert);

	/* pPkey should be freed by the caller */
	return pPkey;
}
/*-----------------------------------------------------------*/

static inline bool prvContextValidate( OtaFileContext_t * C )
{
    return( ( C != NULL ) &&
            ( C->pFile != NULL ) ); /*lint !e9034 Comparison is correct for file pointer type. */
}

/* Used to set the high bit of Windows error codes for a negative return value. */
#define OTA_PAL_INT16_NEGATIVE_MASK    ( 1 << 15 )

/* Size of buffer used in file operations on this platform (Windows). */
#define OTA_PAL_WIN_BUF_SIZE ( ( size_t ) 4096UL )

/* Attempt to create a new receive file for the file chunks as they come in. */

OtaErr_t prvPAL_CreateFileForRx( OtaFileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CreateFileForRx" );

    OtaErr_t eResult = OTA_ERR_UNINITIALIZED; /* For MISRA mandatory. */

    if( C != NULL )
    {
        if ( C->pFilePath != NULL )
        {
            C->pFile = fopen( ( const char * )C->pFilePath, "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

            if ( C->pFile != NULL )
            {
                eResult = OTA_ERR_NONE;
                LogInfo( ( "[%s] Receive file created.\r\n", OTA_METHOD_NAME ) );
            }
            else
            {
                eResult = ( OTA_ERR_RX_FILE_CREATE_FAILED | ( errno & OTA_PAL_ERR_MASK ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                           * Errno is being used in accordance with host API documentation.
                                                                                           * Bitmasking is being used to preserve host API error with library status code. */
                LogError( ( "[%s] ERROR - Failed to start operation: already active!\r\n", OTA_METHOD_NAME ) );
            }
        }
        else
        {
            eResult = OTA_ERR_RX_FILE_CREATE_FAILED;
            LogError( ( "[%s] ERROR - Invalid file path provided.\r\n", OTA_METHOD_NAME ) );
        }
    }
    else
    {
        eResult = OTA_ERR_RX_FILE_CREATE_FAILED;
        LogError( ( "[%s] ERROR - Invalid context provided.\r\n", OTA_METHOD_NAME ) );
    }

    return eResult; /*lint !e480 !e481 Exiting function without calling fclose.
                     * Context file handle state is managed by this API. */
}


/* Abort receiving the specified OTA update by closing the file. */

OtaErr_t prvPAL_Abort( OtaFileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_Abort" );

    /* Set default return status to uninitialized. */
    OtaErr_t eResult = OTA_ERR_UNINITIALIZED;
    int32_t lFileCloseResult;

    if( NULL != C )
    {
        /* Close the OTA update file if it's open. */
        if( NULL != C->pFile )
        {
            lFileCloseResult = fclose( C->pFile ); /*lint !e482 !e586
                                                      * Context file handle state is managed by this API. */
            C->pFile = NULL;

            if( 0 == lFileCloseResult )
            {
                LogInfo( ( "[%s] OK\r\n", OTA_METHOD_NAME ) );
                eResult = OTA_ERR_NONE;
            }
            else /* Failed to close file. */
            {
                LogError( ( "[%s] ERROR - Closing file failed.\r\n", OTA_METHOD_NAME ) );
                eResult = ( OTA_ERR_FILE_ABORT | ( errno & OTA_PAL_ERR_MASK ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                  * Errno is being used in accordance with host API documentation.
                                                                                  * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            /* Nothing to do. No open file associated with this context. */
            eResult = OTA_ERR_NONE;
        }
    }
    else /* Context was not valid. */
    {
        LogError( ( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME ) );
        eResult = OTA_ERR_FILE_ABORT;
    }

    return eResult;
}

/* Write a block of data to the specified file. */
int16_t prvPAL_WriteBlock( OtaFileContext_t * const C,
                           uint32_t ulOffset,
                           uint8_t * const pacData,
                           uint32_t ulBlockSize )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_WriteBlock" );

    int32_t lResult = 0;

    if( prvContextValidate( C ) )
    {
        lResult = fseek( C->pFile, ulOffset, SEEK_SET ); /*lint !e586 !e713 !e9034
                                                            * C standard library call is being used for portability. */

        if( 0 == lResult )
        {
            lResult = fwrite( pacData, 1, ulBlockSize, C->pFile ); /*lint !e586 !e713 !e9034
                                                                      * C standard library call is being used for portability. */

            if( lResult < 0 )
            {
                LogError( ( "[%s] ERROR - fwrite failed\r\n", OTA_METHOD_NAME ) );
                /* Mask to return a negative value. */
                lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                                * Errno is being used in accordance with host API documentation.
                                                                * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            LogError( ( "[%s] ERROR - fseek failed\r\n", OTA_METHOD_NAME ) );
            /* Mask to return a negative value. */
            lResult = OTA_PAL_INT16_NEGATIVE_MASK | errno; /*lint !e40 !e9027
                                                            * Errno is being used in accordance with host API documentation.
                                                            * Bitmasking is being used to preserve host API error with library status code. */
        }
    }
    else /* Invalid context or file pointer provided. */
    {
        LogError( ( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME ) );
        lResult = -1; /*TODO: Need a negative error code from the PAL here. */
    }

    return ( int16_t ) lResult;
}

/* Close the specified file. This shall authenticate the file if it is marked as secure. */

OtaErr_t prvPAL_CloseFile( OtaFileContext_t * const C )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_CloseFile" );

    OtaErr_t eResult = OTA_ERR_NONE;
    int32_t lWindowsError = 0;

    if( prvContextValidate( C ) )
    {
        if( C->pSignature != NULL )
        {
            /* Verify the file signature, close the file and return the signature verification result. */
            eResult = prvPAL_CheckFileSignature( C );
        }
        else
        {
            LogError( ( "[%s] ERROR - NULL OTA Signature structure.\r\n", OTA_METHOD_NAME ) );
            eResult = OTA_ERR_SIGNATURE_CHECK_FAILED;
        }

        /* Close the file. */
        lWindowsError = fclose( C->pFile ); /*lint !e482 !e586
                                               * C standard library call is being used for portability. */
        C->pFile = NULL;

        if( lWindowsError != 0 )
        {
            LogError( ( "[%s] ERROR - Failed to close OTA update file.\r\n", OTA_METHOD_NAME ) );
            eResult = ( OTA_ERR_FILE_CLOSE | ( errno & OTA_PAL_ERR_MASK ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                              * Errno is being used in accordance with host API documentation.
                                                                              * Bitmasking is being used to preserve host API error with library status code. */
        }

        if( eResult == OTA_ERR_NONE )
        {
            LogInfo( ( "[%s] %s signature verification passed.\r\n", OTA_METHOD_NAME, OTA_JsonFileSignatureKey ) );

            prvPAL_SetPlatformImageState( C, OtaImageStateTesting );
        }
        else
        {
            LogError( (  "[%s] ERROR - Failed to pass %s signature verification: %d.\r\n", OTA_METHOD_NAME,
                        OTA_JsonFileSignatureKey, eResult ) );

			/* If we fail to verify the file signature that means the image is not valid. We need to set the image state to aborted. */
			prvPAL_SetPlatformImageState( C, OtaImageStateAborted );

        }
    }
    else /* Invalid OTA Context. */
    {
        /* FIXME: Invalid error code for a null file context and file handle. */
        LogError( ( "[%s] ERROR - Invalid context.\r\n", OTA_METHOD_NAME ) );
        eResult = OTA_ERR_FILE_CLOSE;
    }

    return eResult;
}


static OtaErr_t Openssl_DigestVerify(EVP_MD_CTX * pSigContext, EVP_PKEY * pPkey, FILE *pFile, Sig256_t * pSignature)
{
    OtaErr_t eResult = OTA_ERR_NONE;
    uint32_t bytesRead;
    uint8_t * pBuf;

    /* Verify an ECDSA-SHA256 signature. */
    if ((pSigContext != NULL) &&
        (pPkey != NULL) &&
        (pFile != NULL) &&
        (1 == EVP_DigestVerifyInit(pSigContext, NULL, EVP_sha256(), NULL, pPkey)))
    {
        LogDebug("[DigestVerify] Started signature verification\r\n");


        pBuf = malloc(OTA_PAL_WIN_BUF_SIZE);  /* can use OPENSSL_malloc() here too */

        if (pBuf != NULL)
        {
            /* Rewind the received file to the beginning. */
            if (fseek(pFile, 0L, SEEK_SET) == 0) /*lint !e586
                                                            * C standard library call is being used for portability. */
            {
                do
                {
                    bytesRead = fread(pBuf, 1, OTA_PAL_WIN_BUF_SIZE, pFile); /*lint !e586
                                                                                        * C standard library call is being used for portability. */
                                                                                        /* Include the file chunk in the signature validation. Zero size is OK. */
                    EVP_DigestVerifyUpdate(pSigContext, pBuf, bytesRead);
                } while (bytesRead > 0UL);

                if (1 != EVP_DigestVerifyFinal(pSigContext,
                    pSignature->data,
                    pSignature->size)) /*lint !e732 !e9034 Allow comparison in this context. */
                {
                    LogError(("File signature check failed at FINAL\n"));
                    eResult = OTA_ERR_SIGNATURE_CHECK_FAILED;
                }

            }
            
            /* Free the temporary file page buffer. This can use OPENSSL_free()*/
            free(pBuf);
        }
        else
        {
            LogError(("Failed to allocate buffer memory.\n"));
            eResult = OTA_ERR_OUT_OF_MEMORY;
        }
    }
    else
    {
        LogError(( "File signature check failed at INIT.\n" ));
        eResult = OTA_ERR_SIGNATURE_CHECK_FAILED;
    }

    return eResult;
}

/********************************************/
/* OPENSSL version
/* Verify the signature of the specified file.
/*********************************************/

static OtaErr_t prvPAL_CheckFileSignature( OtaFileContext_t * const C )
{
    OtaErr_t eResult = OTA_ERR_NONE;
    EVP_PKEY * pPkey = NULL;
    EVP_MD_CTX * pSigContext = NULL;
    int rc = 0;

    if( prvContextValidate( C ) )
    {
        /* Extract the signer cert from the file */
        pPkey = Openssl_GetPkeyFromCertificate( ( const uint8_t * const ) C->pCertFilepath );

        /* Create a new signature context for verification purpose */
        pSigContext = EVP_MD_CTX_new();

        if ( (pPkey != NULL) && (pSigContext != NULL ) )
        {
            /* Verify an ECDSA-SHA256 signature. */
			eResult = Openssl_DigestVerify(pSigContext, pPkey, C->pFile, C->pSignature);
        }
        else
		{
            if( pSigContext == NULL )
			{
                LogError(( "File signature check failed at NEW sig context.\n" ));
                eResult = OTA_ERR_SIGNATURE_CHECK_FAILED;
            }
            else
            {
                LogError(( "File signature check failed at EXTRACT pkey from signer cert\n" ));
                eResult = OTA_ERR_BAD_SIGNER_CERT;
            }
        }

        /* Free up objects */
        EVP_MD_CTX_free(pSigContext);
        EVP_PKEY_free(pPkey);
    }
    else
    {
        /* FIXME: Invalid error code for a NULL file context. */
        LogError(( "Invalid OTA file context.\r\n" ));
        /* Invalid OTA context or file pointer. */
        eResult = OTA_ERR_NULL_FILE_PTR;
    }

    return eResult;
}


/*-----------------------------------------------------------*/

OtaErr_t prvPAL_ResetDevice( OtaFileContext_t * const C )
{
    OtaErr_t eResult = OTA_ERR_NONE;
    
    if( !prvContextValidate( C ) )
    {
        /* FIXME: Invalid error code for a NULL file context. */
        LogError(( "Invalid OTA file context.\r\n" ));
        /* Invalid OTA context or file pointer. */
        eResult = OTA_ERR_NULL_FILE_PTR;
    }

    /* Return no error.  Windows implementation does not reset device. */
    return eResult;
}

/*-----------------------------------------------------------*/

OtaErr_t prvPAL_ActivateNewImage( OtaFileContext_t * const C )
{
    OtaErr_t eResult = OTA_ERR_NONE;

    if( !prvContextValidate( C ) )
    {
        /* FIXME: Invalid error code for a NULL file context. */
        LogError(( "Invalid OTA file context.\r\n" ));
        /* Invalid OTA context or file pointer. */
        eResult = OTA_ERR_NULL_FILE_PTR;
    }
    
    /* Return no error. Windows implementation simply does nothing on activate.
     * To run the new firmware image, double click the newly downloaded exe */
    return eResult;
}


/*
 * Set the final state of the last transferred (final) OTA file (or bundle).
 * On Windows, the state of the OTA image is stored in PlaformImageState.txt.
 */

OtaErr_t prvPAL_SetPlatformImageState( OtaFileContext_t * const C, OtaImageState_t eState )
{
    DEFINE_OTA_METHOD_NAME( "prvPAL_SetPlatformImageState" );

    OtaErr_t eResult = OTA_ERR_NONE;
    FILE * pstPlatformImageState;

    if( !prvContextValidate( C ) )
    {
        /* FIXME: Invalid error code for a NULL file context. */
        LogError(( "Invalid OTA file context.\r\n" ));
        /* Invalid OTA context or file pointer. */
        eResult = OTA_ERR_NULL_FILE_PTR;
    }
    else if( eState != OtaImageStateUnknown && eState <= OtaLastImageState )
    {
        pstPlatformImageState = fopen( "PlatformImageState.txt", "w+b" ); /*lint !e586
                                                                           * C standard library call is being used for portability. */

        if( pstPlatformImageState != NULL )
        {
            /* Write the image state to PlatformImageState.txt. */
            if( 1 != fwrite( &eState, sizeof( OtaImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                                * C standard library call is being used for portability. */
            {
                LogError( ( "[%s] ERROR - Unable to write to image state file.\r\n", OTA_METHOD_NAME );
                eResult = ( OTA_ERR_BAD_IMAGE_STATE | ( errno & OTA_PAL_ERR_MASK ) ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                      * Errno is being used in accordance with host API documentation.
                                                                                      * Bitmasking is being used to preserve host API error with library status code. */
            }

            /* Close PlatformImageState.txt. */
            if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586 Allow call in this context. */
            {
                LogError( ( "[%s] ERROR - Unable to close image state file.\r\n", OTA_METHOD_NAME ) );
                eResult = ( OTA_ERR_BAD_IMAGE_STATE | ( errno & OTA_PAL_ERR_MASK ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                      * Errno is being used in accordance with host API documentation.
                                                                                      * Bitmasking is being used to preserve host API error with library status code. */
            }
        }
        else
        {
            LogError( ( "[%s] ERROR - Unable to open image state file.\r\n", OTA_METHOD_NAME ) );
            eResult = ( OTA_ERR_BAD_IMAGE_STATE | ( errno & OTA_PAL_ERR_MASK ) ); /*lint !e40 !e737 !e9027 !e9029
                                                                                  * Errno is being used in accordance with host API documentation.
                                                                                  * Bitmasking is being used to preserve host API error with library status code. */
        }
    } /*lint !e481 Allow fopen and fclose calls in this context. */
    else /* Image state invalid. */
    {
        LogError( ( "[%s] ERROR - Invalid image state provided.\r\n", OTA_METHOD_NAME ) );
        eResult = OTA_ERR_BAD_IMAGE_STATE;
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
OtaPalImageState_t prvPAL_GetPlatformImageState( OtaFileContext_t * const C )
{
    /* FIXME: This function should return OtaPalImageState_t, but it doesn't. */
    DEFINE_OTA_METHOD_NAME( "prvPAL_GetPlatformImageState" );

    FILE * pstPlatformImageState;
	OtaImageState_t eSavedAgentState = OtaImageStateUnknown;
	OtaPalImageState_t ePalState = OtaPalImageStateUnknown;

    if( !prvContextValidate( C ) )
    {
        /* FIXME: Invalid error code for a NULL file context. */
        LogError(( "Invalid OTA file context.\r\n" ));
        /* Invalid OTA context or file pointer. */
        ePalState = OtaPalImageStateUnknown;
    }
    else 
    {

        pstPlatformImageState = fopen( "PlatformImageState.txt", "r+b" ); /*lint !e586
                                                                        * C standard library call is being used for portability. */

        if( pstPlatformImageState != NULL )
        {
            if( 1 != fread( &eSavedAgentState, sizeof( OtaImageState_t ), 1, pstPlatformImageState ) ) /*lint !e586 !e9029
                                                                                            * C standard library call is being used for portability. */
            {
                /* If an error occured reading the file, mark the state as aborted. */
                LogError( ( "[%s] ERROR - Unable to read image state file.\r\n", OTA_METHOD_NAME ) );
                ePalState = ( OtaPalImageStateInvalid | (errno & OTA_PAL_ERR_MASK) );
            }
            else
            {
                switch (eSavedAgentState)
                {
                    case OtaImageStateTesting:
                        ePalState = OtaPalImageStatePendingCommit;
                        break;
                    case OtaImageStateAccepted:
                        ePalState = OtaPalImageStateValid;
                        break;
                    case OtaImageStateRejected:
                    case OtaImageStateAborted:
                    default:
                        ePalState = OtaPalImageStateInvalid;
                        break;
                }
            }


            if( 0 != fclose( pstPlatformImageState ) ) /*lint !e586
                                                        * C standard library call is being used for portability. */
            {
                LogError( ( "[%s] ERROR - Unable to close image state file.\r\n", OTA_METHOD_NAME ) );
                ePalState = ( OtaPalImageStateInvalid | ( errno & OTA_PAL_ERR_MASK ) );
            }
        }
        else
        {
            /* If no image state file exists, assume a factory image. */
            ePalState = OtaPalImageStateValid; /*lint !e64 Allow assignment. */
        }
    }

    return ePalState; /*lint !e64 !e480 !e481 I/O calls and return type are used per design. */
}

/*-----------------------------------------------------------*/

/* Provide access to private members for testing. */
#ifdef AMAZON_FREERTOS_ENABLE_UNIT_TESTS
#include "aws_ota_pal_test_access_define.h"
#endif
