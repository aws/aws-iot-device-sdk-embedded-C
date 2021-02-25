/*
 * OTA PAL V2.1.0 for POSIX
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



/* OTA PAL implementation for POSIX platform. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <assert.h>
#include <libgen.h>
#include <unistd.h>

#include "ota.h"
#include "ota_pal_posix.h"

#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/x509.h>
#include <openssl/pem.h>

/**
 * @brief Code signing certificate
 *
 * The certificate is used for OTA image signing.  If a platform does not support a file
 * system the signing certificate can be pasted here for testing purpose.
 *
 * PEM-encoded code signer certificate
 *
 * Must include the PEM header and footer:
 * "-----BEGIN CERTIFICATE-----\n"
 * "...base64 data...\n"
 * "-----END CERTIFICATE-----\n";
 */
static const char signingcredentialSIGNING_CERTIFICATE_PEM[] = "Paste code signing certificate here";

/**
 * @brief Size of buffer used in file operations on this platform (POSIX).
 */
#define OTA_PAL_POSIX_BUF_SIZE           ( ( size_t ) 4096U )

/**
 * @brief Name of the file used for storing platform image state.
 */
#define OTA_PLATFORM_IMAGE_STATE_FILE    "PlatformImageState.txt"

/**
 * @brief Specify the OTA signature algorithm we support on this platform.
 */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/**
 * @brief Read the specified signer certificate from the filesystem into a local buffer. The allocated
 * memory becomes the property of the caller who is responsible for freeing it.
 */
static EVP_PKEY * Openssl_GetPkeyFromCertificate( uint8_t * pCertFilePath );

/**
 * @brief Verify the signature of the input content with OpenSSL.
 */
static OtaPalMainStatus_t Openssl_DigestVerify( EVP_MD_CTX * pSigContext,
                                                EVP_PKEY * pPkey,
                                                FILE * pFile,
                                                Sig256_t * pSignature );

/**
 * @brief Verify the signature of the specified file using OpenSSL.
 */
static OtaPalStatus_t otaPal_CheckFileSignature( OtaFileContext_t * const C );

/**
 * @brief Get the absolute file path from the environment.
 *
 * @param realFilePath Buffer to store the file path + file name.
 * @param pFilePath File name to append to the end of current path.
 */
static OtaPalPathGenStatus_t getFilePathFromCWD( char * realFilePath,
                                                 const char * pFilePath );

/*-----------------------------------------------------------*/

static EVP_PKEY * Openssl_GetPkeyFromCertificate( uint8_t * pCertFilePath )
{
    BIO * pBio = NULL;
    X509 * pCert = NULL;
    EVP_PKEY * pPkey = NULL;
    int32_t rc = 0;

    /* Read the cert file */
    pBio = BIO_new( BIO_s_file() );

    if( pBio != NULL )
    {
        /* coverity[misra_c_2012_rule_10_1_violation] */
        rc = BIO_read_filename( pBio, pCertFilePath );

        if( rc != 1 )
        {
            LogDebug( ( " No cert file, reading signer cert from header file\n" ) );

            /* Get the signer cert from a predefined PEM string */
            BIO_free_all( pBio );
            pBio = BIO_new( BIO_s_mem() );

            if( pBio != NULL )
            {
                rc = BIO_puts( pBio, signingcredentialSIGNING_CERTIFICATE_PEM );

                if( rc <= 0 )
                {
                    LogError( ( "Failed to write a PEM string to BIO stream" ) );
                }
            }
            else
            {
                LogError( ( "Failed to read certificate from a PEM string." ) );
            }
        }
        else
        {
            LogDebug( ( "Opened certificate file." ) );
        }
    }

    if( ( pBio != NULL ) && ( rc > 0 ) )
    {
        pCert = PEM_read_bio_X509( pBio, NULL, NULL, NULL );

        if( pCert != NULL )
        {
            LogDebug( ( "Getting the pkey from the X509 cert." ) );

            /* Extract the public key */
            pPkey = X509_get_pubkey( pCert );

            if( pPkey == NULL )
            {
                LogError( ( "Failed to get pkey from the signer cert." ) );
            }
        }
        else
        {
            LogError( ( "Failed to load cert from either file or predefined string." ) );
        }
    }
    else
    {
        LogError( ( "Failed to read signer cert." ) );
    }

    BIO_free_all( pBio );
    X509_free( pCert );

    /* pPkey should be freed by the caller */
    return pPkey;
}


static OtaPalMainStatus_t Openssl_DigestVerifyStart( EVP_MD_CTX * pSigContext,
                                                     EVP_PKEY * pPkey,
                                                     FILE * pFile,
                                                     uint8_t ** pBuf )
{
    OtaPalMainStatus_t mainErr = OtaPalSignatureCheckFailed;

    assert( pBuf != NULL );
    assert( ( pSigContext != NULL ) && ( pPkey != NULL ) );

    /* Verify an ECDSA-SHA256 signature. */
    if( ( pFile != NULL ) &&
        ( 1 == EVP_DigestVerifyInit( pSigContext, NULL, EVP_sha256(), NULL, pPkey ) ) )
    {
        LogDebug( ( "Started signature verification." ) );

        *pBuf = OPENSSL_malloc( OTA_PAL_POSIX_BUF_SIZE );

        if( *pBuf == NULL )
        {
            LogError( ( "Failed to allocate buffer memory." ) );
            mainErr = OtaPalOutOfMemory;
        }
        else
        {
            mainErr = OtaPalSuccess;
        }
    }
    else
    {
        LogError( ( "File signature check failed at INIT." ) );
    }

    return mainErr;
}

static bool Openssl_DigestVerifyUpdate( EVP_MD_CTX * pSigContext,
                                        FILE * pFile,
                                        uint8_t * pBuf )
{
    size_t bytesRead;

    do
    {
        /* POSIX port using standard library */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        bytesRead = fread( pBuf, 1U, OTA_PAL_POSIX_BUF_SIZE, pFile );

        assert( bytesRead <= OTA_PAL_POSIX_BUF_SIZE );

        /* feof returns non-zero if end of file is reached, otherwise it returns 0. When
         * bytesRead is not equal to OTA_PAL_POSIX_BUF_SIZE, we should be reading last
         * chunk and reach to end of file. */

        /* POSIX port using standard library */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        if( ( bytesRead < OTA_PAL_POSIX_BUF_SIZE ) && ( 0 == feof( pFile ) ) )
        {
            break;
        }

        /* Include the file chunk in the signature validation. Zero size is OK. */
        if( 1 != EVP_DigestVerifyUpdate( pSigContext, pBuf, bytesRead ) )
        {
            break;
        }
    } while( bytesRead > 0UL );

    /* POSIX port using standard library */
    /* coverity[misra_c_2012_rule_21_6_violation] */
    return( 0 != feof( pFile ) ? true : false );
}

static OtaPalMainStatus_t Openssl_DigestVerify( EVP_MD_CTX * pSigContext,
                                                EVP_PKEY * pPkey,
                                                FILE * pFile,
                                                Sig256_t * pSignature )
{
    OtaPalMainStatus_t mainErr = OtaPalSignatureCheckFailed;
    OtaPalMainStatus_t startErr;
    uint8_t * pBuf;

    startErr = Openssl_DigestVerifyStart( pSigContext, pPkey, pFile, &pBuf );

    if( OtaPalSuccess == startErr )
    {
        /* Rewind the received file to the beginning. */
        /* POSIX port using standard library */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        if( fseek( pFile, 0L, SEEK_SET ) == 0 )
        {
            bool eof = Openssl_DigestVerifyUpdate( pSigContext, pFile, pBuf );

            if( ( eof == true ) && ( 1 == EVP_DigestVerifyFinal( pSigContext,
                                                                 pSignature->data,
                                                                 pSignature->size ) ) )
            {
                mainErr = OtaPalSuccess;
            }
            else
            {
                LogError( ( "File signature check failed at FINAL" ) );
            }
        }

        /* Free the temporary file page buffer. */
        OPENSSL_free( pBuf );
    }
    else
    {
        mainErr = startErr;
    }

    return mainErr;
}

static OtaPalStatus_t otaPal_CheckFileSignature( OtaFileContext_t * const C )
{
    OtaPalMainStatus_t mainErr = OtaPalSignatureCheckFailed;
    EVP_PKEY * pPkey = NULL;
    EVP_MD_CTX * pSigContext = NULL;

    assert( C != NULL );

    /* Extract the signer cert from the file. */
    pPkey = Openssl_GetPkeyFromCertificate( C->pCertFilepath );

    /* Create a new signature context for verification purpose. */
    pSigContext = EVP_MD_CTX_new();

    if( ( pPkey != NULL ) && ( pSigContext != NULL ) )
    {
        /* Verify the signature. */
        mainErr = Openssl_DigestVerify( pSigContext, pPkey, C->pFile, C->pSignature );
    }
    else
    {
        if( pSigContext == NULL )
        {
            LogError( ( "File signature check failed at NEW sig context." ) );
        }
        else
        {
            LogError( ( "File signature check failed at EXTRACT pkey from signer certificate." ) );
            mainErr = OtaPalBadSignerCert;
        }
    }

    /* Free up objects */
    EVP_MD_CTX_free( pSigContext );
    EVP_PKEY_free( pPkey );

    return OTA_PAL_COMBINE_ERR( mainErr, 0 );
}

static OtaPalPathGenStatus_t getFilePathFromCWD( char * pCompleteFilePath,
                                                 const char * pFileName )
{
    char * pCurrentDir = NULL;
    OtaPalPathGenStatus_t status = OtaPalFileGenSuccess;

    /* Get current directory. */
    pCurrentDir = getcwd( pCompleteFilePath, OTA_FILE_PATH_LENGTH_MAX - 1 );

    if( pCurrentDir == NULL )
    {
        LogError( ( "Failed to get current working directory: %s", strerror( errno ) ) );
        status = OtaPalCWDFailed;
    }
    else
    {
        /* Add the filename . */
        if( strlen( pCompleteFilePath ) + strlen( pFileName ) + 2U > OTA_FILE_PATH_LENGTH_MAX )
        {
            LogError( ( "Insufficient space to generate file path" ) );
            status = OtaPalBufferInsufficient;
        }
        else
        {
            strcat( pCompleteFilePath, "/" );
            strcat( pCompleteFilePath, pFileName );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

OtaPalStatus_t otaPal_Abort( OtaFileContext_t * const C )
{
    /* Set default return status to uninitialized. */
    OtaPalMainStatus_t mainErr = OtaPalUninitialized;
    int32_t subErr = 0;
    int32_t lFileCloseResult;

    if( NULL != C )
    {
        /* Close the OTA update file if it's open. */
        if( NULL != C->pFile )
        {
            /* POSIX port using standard library */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            lFileCloseResult = fclose( C->pFile );
            C->pFile = NULL;

            if( 0 == lFileCloseResult )
            {
                LogInfo( ( "Closed file." ) );
                mainErr = OtaPalSuccess;
            }
            else /* Failed to close file. */
            {
                LogError( ( "Failed to close file." ) );
                mainErr = OtaPalFileAbort;
                subErr = errno;
            }
        }
        else
        {
            /* Nothing to do. No open file associated with this context. */
            mainErr = OtaPalSuccess;
        }
    }
    else /* Context was not valid. */
    {
        LogError( ( "Parameter check failed: Input is NULL." ) );
        mainErr = OtaPalFileAbort;
    }

    return OTA_PAL_COMBINE_ERR( mainErr, subErr );
}

OtaPalStatus_t otaPal_CreateFileForRx( OtaFileContext_t * const C )
{
    OtaPalStatus_t result = OTA_PAL_COMBINE_ERR( OtaPalUninitialized, 0 );
    char realFilePath[ OTA_FILE_PATH_LENGTH_MAX ];
    OtaPalPathGenStatus_t status = OtaPalFileGenSuccess;

    if( C != NULL )
    {
        if( C->pFilePath != NULL )
        {
            if( C->pFilePath[ 0 ] != ( uint8_t ) '/' )
            {
                status = getFilePathFromCWD( realFilePath, ( const char * ) C->pFilePath );
            }
            else
            {
                ( void ) strncpy( realFilePath, ( const char * ) C->pFilePath, strlen( ( const char * ) C->pFilePath ) + 1U );
            }

            if( status == OtaPalFileGenSuccess )
            {
                /* POSIX port using standard library */
                /* coverity[misra_c_2012_rule_21_6_violation] */
                C->pFile = fopen( ( const char * ) realFilePath, "w+b" );

                if( C->pFile != NULL )
                {
                    result = OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
                    LogInfo( ( "Receive file created." ) );
                }
                else
                {
                    result = OTA_PAL_COMBINE_ERR( OtaPalRxFileCreateFailed, errno );
                    LogError( ( "Failed to start operation: Operation already started. failed to open -- %s Path ", C->pFilePath ) );
                }
            }
            else
            {
                LogError( ( "Could not generate the absolute path for the file" ) );
                result = OTA_PAL_COMBINE_ERR( OtaPalRxFileCreateFailed, 0 );
            }
        }
        else
        {
            result = OTA_PAL_COMBINE_ERR( OtaPalRxFileCreateFailed, 0 );
            LogError( ( "Invalid file path provided." ) );
        }
    }
    else
    {
        result = OTA_PAL_COMBINE_ERR( OtaPalRxFileCreateFailed, 0 );
        LogError( ( "Invalid context provided." ) );
    }

    /* Exiting function without calling fclose. Context file handle state is managed by this API. */
    return result;
}

OtaPalStatus_t otaPal_CloseFile( OtaFileContext_t * const C )
{
    int32_t filerc = 0;
    OtaPalMainStatus_t mainErr = OtaPalSuccess;
    OtaPalSubStatus_t subErr = 0;
    OtaPalStatus_t result;

    if( C != NULL )
    {
        if( C->pSignature != NULL )
        {
            /* Verify the file signature, close the file and return the signature verification result. */
            result = otaPal_CheckFileSignature( C );
            mainErr = OTA_PAL_MAIN_ERR( result );
            subErr = OTA_PAL_SUB_ERR( result );
        }
        else
        {
            LogError( ( "Parameter check failed: OTA signature structure is NULL." ) );
            mainErr = OtaPalSignatureCheckFailed;
        }

        /* Close the file. */
        /* POSIX port using standard library */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        filerc = fclose( C->pFile );
        C->pFile = NULL;

        if( filerc != 0 )
        {
            LogError( ( "Failed to close OTA update file." ) );
            mainErr = OtaPalFileClose;
            subErr = ( uint32_t ) errno;
        }

        if( mainErr == OtaPalSuccess )
        {
            LogInfo( ( "%s signature verification passed.", OTA_JsonFileSignatureKey ) );

            ( void ) otaPal_SetPlatformImageState( C, OtaImageStateTesting );
        }
        else
        {
            LogError( ( "Failed to pass %s signature verification: %d.",
                        OTA_JsonFileSignatureKey, OTA_PAL_COMBINE_ERR( mainErr, subErr ) ) );

            /* If we fail to verify the file signature that means the image is not valid. We need to set the image state to aborted. */
            ( void ) otaPal_SetPlatformImageState( C, OtaImageStateAborted );
        }
    }
    else /* Invalid OTA Context. */
    {
        LogError( ( "Failed to close file: "
                    "Parameter check failed: "
                    "Invalid context." ) );
        mainErr = OtaPalFileClose;
    }

    return OTA_PAL_COMBINE_ERR( mainErr, subErr );
}

int16_t otaPal_WriteBlock( OtaFileContext_t * const C,
                           uint32_t ulOffset,
                           uint8_t * const pcData,
                           uint32_t ulBlockSize )
{
    int32_t filerc = 0;
    size_t writeSize = 0;

    if( C != NULL )
    {
        /* POSIX port using standard library */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        filerc = fseek( C->pFile, ( int64_t ) ulOffset, SEEK_SET );

        if( 0 == filerc )
        {
            /* POSIX port using standard library */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            writeSize = fwrite( pcData, 1, ulBlockSize, C->pFile );

            if( writeSize != ulBlockSize )
            {
                LogError( ( "Failed to write block to file: "
                            "fwrite returned error: "
                            "errno=%d", errno ) );

                filerc = -1;
            }
            else
            {
                filerc = ( int32_t ) writeSize;
            }
        }
        else
        {
            LogError( ( "fseek failed. fseek returned errno = %d", errno ) );
            filerc = -1;
        }
    }
    else /* Invalid context or file pointer provided. */
    {
        LogError( ( "Invalid context." ) );
        filerc = -1;
    }

    return ( int16_t ) filerc;
}

/* Return no error. POSIX implementation simply does nothing on activate. */
OtaPalStatus_t otaPal_ActivateNewImage( OtaFileContext_t * const C )
{
    ( void ) C;

    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

/* Set the final state of the last transferred (final) OTA file (or bundle).
 * On POSIX, the state of the OTA image is stored in PlatformImageState.txt. */
OtaPalStatus_t otaPal_SetPlatformImageState( OtaFileContext_t * const C,
                                             OtaImageState_t eState )
{
    OtaPalMainStatus_t mainErr = OtaPalBadImageState;
    OtaPalPathGenStatus_t status = OtaPalFileGenSuccess;
    int32_t subErr = 0;
    FILE * pPlatformImageState = NULL;
    char imageStateFile[ OTA_FILE_PATH_LENGTH_MAX ] = { 0 };

    ( void ) C;

    if( ( eState != OtaImageStateUnknown ) && ( eState <= OtaLastImageState ) )
    {
        /* Get file path for the image state file. */
        status = getFilePathFromCWD( imageStateFile, OTA_PLATFORM_IMAGE_STATE_FILE );

        if( status == OtaPalFileGenSuccess )
        {
            /* POSIX port using standard library */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            pPlatformImageState = fopen( imageStateFile, "w+b" );
        }
        else
        {
            LogError( ( "Could not generate the absolute path for the file" ) );
        }

        if( pPlatformImageState != NULL )
        {
            /* Write the image state to PlatformImageState.txt. */
            /* POSIX port using standard library */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            if( 1UL == fwrite( &eState, sizeof( OtaImageState_t ), 1, pPlatformImageState ) )
            {
                /* Close PlatformImageState.txt. */
                /* POSIX port using standard library */
                /* coverity[misra_c_2012_rule_21_6_violation] */
                if( 0 == fclose( pPlatformImageState ) )
                {
                    mainErr = OtaPalSuccess;
                }
                else
                {
                    LogError( ( "Unable to close image state file." ) );
                    subErr = errno;
                }
            }
            else
            {
                LogError( ( "Unable to write to image state file. error-- %d", errno ) );
                subErr = errno;

                /* The file should be closed, but errno passed out is fwrite error */
                /* POSIX port using standard library */
                /* coverity[misra_c_2012_rule_21_6_violation] */
                ( void ) fclose( pPlatformImageState );
            }
        }
        else
        {
            LogError( ( "Unable to open image state file. Path: %s error: %s", imageStateFile, strerror( errno ) ) );
            subErr = errno;
        }
    }
    else /* Image state invalid. */
    {
        LogError( ( "Invalid image state provided." ) );
    }

    /* Allow calls to fopen and fclose in this context. */
    return OTA_PAL_COMBINE_ERR( mainErr, subErr );
}

OtaPalStatus_t otaPal_ResetDevice( OtaFileContext_t * const C )
{
    ( void ) C;

    /* Return no error.  POSIX implementation does not reset device. */
    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

/* Get the state of the currently running image.
 *
 * On POSIX, this is simulated by looking for and reading the state from
 * the PlatformImageState.txt file in the current working directory.
 *
 * We read this at OTA_Init time so we can tell if the MCU image is in self
 * test mode. If it is, we expect a successful connection to the OTA services
 * within a reasonable amount of time. If we don't satisfy that requirement,
 * we assume there is something wrong with the firmware and reset the device,
 * causing it to rollback to the previous code. On POSIX, this is not
 * fully simulated as there is no easy way to reset the simulated device.
 */
OtaPalImageState_t otaPal_GetPlatformImageState( OtaFileContext_t * const C )
{
    FILE * pPlatformImageState = NULL;
    OtaImageState_t eSavedAgentState = OtaImageStateUnknown;
    OtaPalImageState_t ePalState = OtaPalImageStateUnknown;
    OtaPalPathGenStatus_t status = OtaPalFileGenSuccess;
    char imageStateFile[ OTA_FILE_PATH_LENGTH_MAX ] = { 0 };

    ( void ) C;

    /* Get file path for the image state file. */
    status = getFilePathFromCWD( imageStateFile, OTA_PLATFORM_IMAGE_STATE_FILE );

    if( status != OtaPalFileGenSuccess )
    {
        LogError( ( "Could not generate the absolute path for the file" ) );
        ePalState = OtaPalImageStateInvalid;
    }
    else
    {
        /* POSIX port using standard library */
        /* coverity[misra_c_2012_rule_21_6_violation] */
        pPlatformImageState = fopen( imageStateFile, "r+b" );

        if( pPlatformImageState != NULL )
        {
            /* POSIX port using standard library */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            if( 1U != fread( &eSavedAgentState, sizeof( OtaImageState_t ), 1, pPlatformImageState ) )
            {
                /* If an error occurred reading the file, mark the state as aborted. */
                LogError( ( "Failed to read image state file." ) );
                ePalState = OtaPalImageStateInvalid;
            }
            else
            {
                if( eSavedAgentState == OtaImageStateTesting )
                {
                    ePalState = OtaPalImageStatePendingCommit;
                }
                else if( eSavedAgentState == OtaImageStateAccepted )
                {
                    ePalState = OtaPalImageStateValid;
                }
                else
                {
                    ePalState = OtaPalImageStateInvalid;
                }
            }

            /* POSIX port using standard library */
            /* coverity[misra_c_2012_rule_21_6_violation] */
            if( 0 != fclose( pPlatformImageState ) )
            {
                LogError( ( "Failed to close image state file." ) );
                ePalState = OtaPalImageStateInvalid;
            }
        }
        else
        {
            /* If no image state file exists, assume a factory image. */
            ePalState = OtaPalImageStateValid; /*lint !e64 Allow assignment. */
        }
    }

    return ePalState;
}

/*-----------------------------------------------------------*/
