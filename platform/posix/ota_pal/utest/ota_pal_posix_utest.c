/*
 * FreeRTOS OTA V1.2.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


/**
 * @file ota_jobParsing_utest.c
 * @brief Unit tests for job parsing functions in ota.c
 */

#include <string.h>
#include <stdbool.h>

#include <sys/stat.h>
#include "unity.h"

/* For accessing OTA private functions. */
#include "ota_private.h"
#include "ota_pal_posix.h"
#include "mock_stdio_api.h"

/* Unit test config. */
#include "ota_utest_config.h"
/* errno error macro. errno.h can't be included in this file due to mocking. */
#define ENOENT 0x02

/* For the otaPal_WriteBlock_WriteManyBlocks test this is the number of blocks of
 * dummyData to write to the non-volatile memory. */
#define testotapalNUM_WRITE_BLOCKS         10

/* For the otaPal_WriteBlock_WriteManyBlocks test this the delay time in ms following
 * the block write loop. */
#define testotapalWRITE_BLOCKS_DELAY_MS    5000

/**
 * @brief Invalid signature for OTA PAL testing.
 */
static const uint8_t ucInvalidSignature[] =
{
    0x30, 0x44, 0x02, 0x20, 0x75, 0xde, 0xa8, 0x1f, 0xca, 0xec, 0xff, 0x16,
    0xbb, 0x38, 0x4b, 0xe3, 0x14, 0xe7, 0xfb, 0x68, 0xf5, 0x3e, 0x86, 0xa2,
    0x71, 0xba, 0x9e, 0x5e, 0x50, 0xbf, 0xb2, 0x7a, 0x9e, 0x00, 0xc6, 0x4d,
    0x02, 0x20, 0x19, 0x72, 0x42, 0x85, 0x2a, 0xac, 0xdf, 0x5a, 0x5e, 0xfa,
    0xad, 0x49, 0x17, 0x5b, 0xce, 0x5b, 0x65, 0x75, 0x08, 0x47, 0x3e, 0x55,
    0xf9, 0x0e, 0xdf, 0x9e, 0x8c, 0xdc, 0x95, 0xdf, 0x63, 0xd2
};
static const int ucInvalidSignatureLength = 70;

/**
 * @brief Valid signature matching the test block in the OTA PAL tests.
 */
static const uint8_t ucValidSignature[] =
{
    0x30, 0x44, 0x02, 0x20, 0x15, 0x6a, 0x68, 0x98, 0xf0, 0x4e, 0x1e, 0x12,
    0x4c, 0xc4, 0xf1, 0x05, 0x22, 0x36, 0xfd, 0xb4, 0xe5, 0x5d, 0x83, 0x08,
    0x2a, 0xf3, 0xa6, 0x7d, 0x32, 0x6b, 0xff, 0x85, 0x27, 0x14, 0x9b, 0xbf,
    0x02, 0x20, 0x26, 0x7d, 0x5f, 0x4d, 0x12, 0xab, 0xec, 0x17, 0xd8, 0x45,
    0xc6, 0x3d, 0x8e, 0xd8, 0x8d, 0x3f, 0x28, 0x26, 0xfd, 0xce, 0x32, 0x34,
    0x17, 0x05, 0x47, 0xb2, 0xf6, 0x84, 0xd5, 0x68, 0x3e, 0x36
};
static const int ucValidSignatureLength = 70;

/**
 * @brief The type of signature method this file defines for the valid signature.
 */
#define otatestSIG_METHOD    otatestSIG_SHA256_ECDSA

/*
 * @brief: This dummy data is prepended by a SHA1 hash generated from the rsa-sha1-signer
 * certificate and keys in tests/common/ota/test_files.
 *
 * The RSA SHA256 signature and ECDSA 256 signature are generated from this entire data
 * block as is.
 */
static uint8_t dummyData[] =
{
    0x83, 0x0b, 0xf0, 0x6a, 0x81, 0xd6, 0xca, 0xd7, 0x08, 0x22, 0x0d, 0x6a,
    0x33, 0xfa, 0x31, 0x9f, 0xa9, 0x5f, 0xb5, 0x26, 0x00, 0x01, 0x02, 0x03,
    0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0c, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
    0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
    0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33,
    0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f
};

/* Global static OTA file context used in every test. This context is reset to all zeros
 * before every test. */
static OtaFileContext_t otaFile;

/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
    /* Always reset the OTA file context before each test. */
    memset( &otaFile, 0, sizeof( otaFile ) );
}

void tearDown( void )
{
    OtaPalMainStatus_t result;

    /* We want to abort the OTA file after every test. This closes the OtaFile. */
    result = otaPal_Abort( &otaFile );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    unlink( "PlatformImageState.txt" );
}

/* ========================================================================== */

/**
 * @brief Test that otaPal_Abort will return correct result code.
 */
void test_OTAPAL_Abort_NullFileContext( void )
{
    OtaPalMainStatus_t result;

    result = OTA_PAL_MAIN_ERR( otaPal_Abort( NULL ) );

    TEST_ASSERT_EQUAL( OtaPalFileAbort, result );
}


/**
 * @brief Test that otaPal_Abort will return correct result code.
 */
void test_OTAPAL_Abort_NullFileHandle( void )
{
    OtaPalMainStatus_t result;

    otaFile.pFile = NULL;
    result = OTA_PAL_MAIN_ERR( otaPal_Abort( &otaFile ) );

    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/**
 * @brief Test that otaPal_Abort will return correct result code.
 */
void test_OTAPAL_Abort_ValidFileHandle( void )
{
    OtaPalMainStatus_t result;
    FILE placeholder_file;
    otaFile.pFilePath = ( uint8_t * ) "placeholder_path";
    otaFile.pFile = &placeholder_file;

    fclose_ExpectAnyArgsAndReturn( 0 );

    result = OTA_PAL_MAIN_ERR( otaPal_Abort( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/**
 * @brief Test that otaPal_Abort will return correct result code.
 */
void test_OTAPAL_Abort_FileCloseFail( void )
{
    OtaPalMainStatus_t result;

    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.pFile = (FILE *) "placeholder";

    fclose_ExpectAnyArgsAndReturn( EOF );

    result = otaPal_Abort( &otaFile );
    TEST_ASSERT_EQUAL( OtaPalFileAbort, OTA_PAL_MAIN_ERR( result ) );
    TEST_ASSERT_EQUAL( ENOENT , OTA_PAL_SUB_ERR( result ) );
}

/**
 * @brief Test that otaPal_Abort will return correct result code.
 */
void test_OTAPAL_Abort_NonExistentFile( void )
{
    OtaPalMainStatus_t result;

    otaFile.pFilePath = ( uint8_t * ) ( "nonexistingfile.bin" );
    result = OTA_PAL_MAIN_ERR( otaPal_Abort( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/**
 * @brief Test that otaPal_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_NullFileContext( void )
{
    OtaPalMainStatus_t result;

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( NULL ) );
    TEST_ASSERT_EQUAL( OtaPalRxFileCreateFailed, result );
}


/**
 * @brief Test that otaPal_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_NullFilePath( void )
{
    OtaPalMainStatus_t result;

    otaFile.pFilePath = NULL;
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );

    TEST_ASSERT_EQUAL( OtaPalRxFileCreateFailed, result );
}

/**
 * @brief Test that otaPal_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_FailedToCreateFile( void )
{
    OtaPalMainStatus_t result;
    FILE placeholder_file;

    otaFile.pFilePath = ( uint8_t * ) "placeholder_path";
    otaFile.pFile = &placeholder_file;

    fopen_ExpectAnyArgsAndReturn( NULL );

    /* Create a file that exists with w+b mode */
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalRxFileCreateFailed, result );
}

/**
 * @brief Test that otaPal_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_ValidFileHandle( void )
{
    OtaPalMainStatus_t result;
    FILE placeholder_file;
    otaFile.pFilePath = ( uint8_t * ) "placeholder_path";

    fopen_ExpectAnyArgsAndReturn( &placeholder_file );
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}


/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_NullFileContext( void )
{
    int16_t result = 0;
    uint8_t data = 0xAA;
    uint32_t blockSize = 1;

    result = otaPal_WriteBlock( NULL, 0, &data, blockSize );
    TEST_ASSERT_EQUAL( -1 , result );
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_WriteSingleByte( void )
{
    int16_t numBytesWritten;
    uint8_t data = 0xAA;
    uint32_t blockSize = 1;

    /* TEST: Write a byte of data. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    fseek_alias_ExpectAnyArgsAndReturn(0);
    fwrite_alias_ExpectAnyArgsAndReturn(blockSize);
    numBytesWritten = otaPal_WriteBlock( &otaFile, 0, &data, blockSize );
    TEST_ASSERT_EQUAL_INT( blockSize, numBytesWritten );
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_WriteMultipleBytes( void )
{
    OtaPalMainStatus_t result;
    int16_t numBytesWritten;
    int index = 0;
    uint8_t pData[] = {0xAA, 0xBB, 0xCC, 0xDD, 0xEE};
    uint32_t blockSize = sizeof( pData[0] );

    /* TEST: Write multiple bytes of data. */
    for( index = 0; index < testotapalNUM_WRITE_BLOCKS; index++ )
    {
        fseek_alias_ExpectAnyArgsAndReturn(0);
        fwrite_alias_ExpectAnyArgsAndReturn( blockSize );
        numBytesWritten = otaPal_WriteBlock( &otaFile, index * blockSize, pData, blockSize );
        TEST_ASSERT_EQUAL_INT( blockSize, numBytesWritten );
    }
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_FseekError( void )
{
    int16_t numBytesWritten;
    uint8_t data = 0xAA;
    uint32_t blockSize = 1;
    const int16_t fseek_error_num = 1; /* fseek returns a non-zero number on error. */
    OtaFileContext_t validFileContext;

    /* TEST: Write a byte of data. */
    fseek_alias_ExpectAnyArgsAndReturn( fseek_error_num );
    numBytesWritten = otaPal_WriteBlock( &validFileContext, 0, &data, blockSize );
    TEST_ASSERT_EQUAL_INT( -1 , numBytesWritten );
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_FwriteError( void )
{
    int16_t numBytesWritten;
    uint8_t data = 0xAA;
    uint32_t blockSize = 1;
    OtaFileContext_t validFileContext;
    const int32_t fseekSuccessReturn = 0; /* fseek returns a zero on success. */
    const size_t fwriteErrorReturn = 0; /* fwrite returns a number less than the requested number of bytes to write on error. */
    const int16_t writeblockErrorReturn = -1;

    fseek_alias_ExpectAnyArgsAndReturn(fseekSuccessReturn);
    fwrite_alias_ExpectAnyArgsAndReturn(fwriteErrorReturn);

    /* fwrite returns a number less than the amount requested to write on error. */
    numBytesWritten = otaPal_WriteBlock( &validFileContext, 0, &data, blockSize );
    TEST_ASSERT_EQUAL_INT( writeblockErrorReturn , numBytesWritten );
}

void test_OTAPAL_CloseFile_ValidSignature( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    Sig256_t sig = { 0 };

    /* We use a dummy file name here because closing the system designated bootable
     * image with content that is not runnable may cause issues. */
    otaFile.pFilePath = ( uint8_t * ) ( "test_happy_path_image.bin" );
    otaFile.fileSize = sizeof( dummyData );
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucValidSignatureLength;
        memcpy( otaFile.pSignature->data, ucValidSignature, ucValidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) OTA_PAL_UTEST_CERT_FILE;

        result = OTA_PAL_MAIN_ERR( otaPal_CloseFile( &otaFile ) );
        TEST_ASSERT_EQUAL_INT( OtaPalSuccess, result );
    }
}


/**
 * @brief Call otaPal_CloseFile with an invalid signature in the file context.
 * The close is called after we have a written a block of dummy data to the file.
 * Verify the correct OTA Agent level error code is returned from otaPal_CloseFile.
 */
void test_OTAPAL_CloseFile_InvalidSignatureBlockWritten( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    Sig256_t sig = { 0 };

    /* Create a local file using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        /* Fill out an incorrect signature. */
        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucInvalidSignatureLength;
        memcpy( otaFile.pSignature->data, ucInvalidSignature, ucInvalidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) OTA_PAL_UTEST_CERT_FILE;

        /* Try to close the file. */
        result = OTA_PAL_MAIN_ERR( otaPal_CloseFile( &otaFile ) );

        if( ( OtaPalBadSignerCert != result ) &&
            ( OtaPalSignatureCheckFailed != result ) &&
            ( OtaPalFileClose != result ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }
    }
}

/**
 * @brief Call otaPal_CloseFile with an invalid signature in the file context.
 * The close is called when no blocks have been written to the file.
 * Verify the correct OTA Agent level error code is returned from otaPal_CloseFile.
 */
void test_OTAPAL_CloseFile_InvalidSignatureNoBlockWritten( void )
{
    OtaPalMainStatus_t result;
    Sig256_t sig = { 0 };

    /* Create a local file using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* Fill out an incorrect signature. */
    otaFile.pSignature = &sig;
    otaFile.pSignature->size = ucInvalidSignatureLength;
    memcpy( otaFile.pSignature->data, ucInvalidSignature, ucInvalidSignatureLength );
    otaFile.pCertFilepath = ( uint8_t * ) OTA_PAL_UTEST_CERT_FILE;

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Try to close the file. */
        result = OTA_PAL_MAIN_ERR( otaPal_CloseFile( &otaFile ) );

        if( ( OtaPalBadSignerCert != result ) &&
            ( OtaPalSignatureCheckFailed != result ) &&
            ( OtaPalFileClose != result ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }
    }
}

/**
 * @brief Call otaPal_CloseFile with a signature verification certificate path does
 * not exist in the system. Verify the correct OTA Agent level error code is returned
 * from otaPal_CloseFile.
 *
 * @note This test is only valid if your device uses a file system in your non-volatile memory.
 * Some devices may revert to using aws_codesigner_certificate.h if a file is not found, but
 * that option is not being enforced.
 */
void test_OTAPAL_CloseFile_NonexistingCodeSignerCertificate( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    Sig256_t sig = { 0 };

    memset( &otaFile, 0, sizeof( otaFile ) );

    /* Create a local file using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        /* Check the signature (not expected to be valid in this case). */
        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucValidSignatureLength;
        memcpy( otaFile.pSignature->data, ucValidSignature, ucValidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) ( "nonexistingfile.crt" );

        result = OTA_PAL_MAIN_ERR( otaPal_CloseFile( &otaFile ) );

        if( ( OtaPalBadSignerCert != result ) &&
            ( OtaPalSignatureCheckFailed != result ) &&
            ( OtaPalFileClose != result ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }
    }
}

/**
 * @brief Test that otaPal_ResetDevice will return correct result code.
 */
void test_OTAPAL_ResetDevice_NullFileContext( void )
{
    OtaPalMainStatus_t result;

    /* Currently there is nothing done inside the function. It's a placeholder. */
    result = OTA_PAL_MAIN_ERR( otaPal_ResetDevice( NULL ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_ActivateNewImage_NullFileContext( void )
{
    OtaPalMainStatus_t result;

    result = OTA_PAL_MAIN_ERR( otaPal_ActivateNewImage( NULL ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

typedef enum
{
    none_fn = 0,
    BIO_s_file_fn,
    BIO_new_fn,
    BIO_s_mem_X509_fn,
    BIO_puts_fn,
    BIO_free_all_fn,
    BIO_ctrl_fn,
    PEM_read_bio_X509_fn,
    X509_get_pubkey_fn,
    X509_free_fn,
    EVP_MD_CTX_new_fn,
    EVP_DigestVerifyInit_fn,
    EVP_DigestVerifyFinal_fn,
    EVP_MD_CTX_free_fn,
    EVP_PKEY_free_fn,
    CRYPTO_free_fn,
    fopen_fn,
    fclose_fn,
    snprintf_fn,
    fread_fn,
    fseek_alias_fn,
    fwrite_alias_fn
} FunctionNames_t;

/**
 * @brief Helper function specify a single point of failure for
 * otaPal_SetPlatformImageState. This needs to be updated each time a mocked
 * function is added or removed to otaPal_SetPlatformImageState. 
 * 
 * Remark: This function assumes specific values for the success and failure of the functions. */
static void OTA_PAL_FailSingleMock( FunctionNames_t funcToFail, OtaImageState_t* pFreadStateToSet )
{
    static FILE dummyFile;

    /* On success, snprintf returns a positive number that is less than the amount of data requested. */
    const int snprintf_success = 0;
    const int snprintf_failure = -1;
    int snprintf_return;
    /* On success, fopen returns a FILE address that is not null. */
    FILE * const fopen_success = &dummyFile;
    FILE * const fopen_failure = NULL;
    FILE * fopen_return;
    /* otaPal_SetPlatformImageState calls write to write a single byte. On success, fwrite will return 1. */
    /* fwrite returns a 0 when reaching the EOF or error. */
    const size_t fwrite_success = 1U;
    const size_t fwrite_failure = 0;
    size_t fwrite_return;
    /* On success, fclose returns a zero. */
    /* On failure, fclose returns EOF. */
    const int fclose_success = 0;
    const int fclose_failure = EOF;
    int fclose_return;
    /* In otaPal_GetPlatformImageState, fread is always called with a 1 for the
       size parameter. So, any number other than 1 is an error. */
    const size_t fread_failure = 0;
    const size_t fread_success = 1;
    size_t fread_return;
    /* fseek returns a zero on success and a non-zero number on failure. */
    const int32_t fseek_success = 0; 
    const int32_t fseek_failure = -1;
    int32_t fseek_return; 


    /* Set the return value for each of the callable functions. */
    fopen_return = ( funcToFail == fopen_fn ) ? fopen_failure : fopen_success;
    fopen_IgnoreAndReturn( fopen_return );

    snprintf_return = ( funcToFail == snprintf_fn ) ? snprintf_failure : snprintf_success;
    snprintf_IgnoreAndReturn( snprintf_return );

    fread_return = ( funcToFail == fread_fn ) ? fread_failure: fread_success;
    fread_IgnoreAndReturn( fread_return );
    fread_ReturnThruPtr_ptr( pFreadStateToSet );

    fseek_return = ( funcToFail == fseek_alias_fn ) ? fseek_failure : fseek_success;
    fseek_alias_IgnoreAndReturn( fseek_return );

    fwrite_return = ( funcToFail == fwrite_alias_fn ) ? fwrite_failure : fwrite_success;
    fwrite_alias_IgnoreAndReturn( fwrite_return );

    fclose_return = ( funcToFail == fclose_fn ) ? fclose_failure : fclose_success;
    fclose_IgnoreAndReturn( fclose_return );
}

/**
 * @brief Verify that otaPal_SetPlatformImageState correctly handles
 *        attempts to set invalid image states.
 */
void test_OTAPAL_SetPlatformImageState_InvalidStates( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t stateToSet;

    stateToSet = OtaImageStateUnknown;
    result = otaPal_SetPlatformImageState( &otaFileContext, stateToSet );
    TEST_ASSERT_EQUAL( OtaPalBadImageState, OTA_PAL_MAIN_ERR( result ) );

    stateToSet = OtaLastImageState + 1;
    result = otaPal_SetPlatformImageState( &otaFileContext, stateToSet );
    TEST_ASSERT_EQUAL( OtaPalBadImageState, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles setting valid
 * image states.
 */
void test_OTAPAL_SetPlatformImageState_HappyPath( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock( none_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles snprintf failing.
 */
void test_OTAPAL_SetPlatformImageState_snprintf_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock( snprintf_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles fopen failing.
 */
void test_OTAPAL_SetPlatformImageState_fopen_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock( fopen_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles fwrite failing.
 */
void test_OTAPAL_SetPlatformImageState_fwrite_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock( fwrite_alias_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles fclose failing.
 */
void test_OTAPAL_SetPlatformImageState_fclose_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock( fclose_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Verify that otaPal_GetPlatformImageState correctly handles a fopen
 *        failure. This test assumes that all other function calls return
 *        success.
 * */
void test_OTAPAL_GetPlatformImageState_fopen_fails( void )
{
    OtaPalImageState_t ePalImageState;
    OtaFileContext_t otaFileContext;

    OTA_PAL_FailSingleMock( fopen_fn, NULL );
    /* The file failed to close, so it is invalid or in an unknown state. */
    ePalImageState = otaPal_GetPlatformImageState( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalImageStateValid, ePalImageState );
}

/**
 * @brief Verify that otaPal_GetPlatformImageState correctly handles a fread
 *        failure. This test assumes that all other function calls return
 *        success.
 * */
void test_OTAPAL_GetPlatformImageState_fread_fails( void )
{
    OtaPalImageState_t ePalImageState;
    OtaFileContext_t otaFileContext;

    OTA_PAL_FailSingleMock( fread_fn , NULL );
    ePalImageState = otaPal_GetPlatformImageState( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalImageStateInvalid, ePalImageState );
}

/**
 * @brief This test validates that the valid states are correctly returned to
 *        the caller.
 * */
void test_OTAPAL_GetPlatformImageState_fclose_fails( void )
{
    OtaPalImageState_t ePalImageState = OtaPalImageStateUnknown;
    OtaFileContext_t otaFileContext;
    FILE dummyFile;

    /* On success, snprintf returns a positive number that is less than the amount of data requested. */
    const int snprintf_success_val = 0;
    /* On success, fopen returns a FILE address that is not null. */
    FILE * const fopen_success_val = &dummyFile;
    /* In otaPal_GetPlatformImageState, fread is always called with a 1 for the
       size parameter. So, any number other than 1 is an error. */
    const size_t fread_success_val = 1;
    /* On failure, fclose returns EOF. */
    const int fclose_fail_val = EOF;

    /* Predefine what functions are expected to be called. */
    snprintf_ExpectAnyArgsAndReturn( snprintf_success_val );
    fopen_ExpectAnyArgsAndReturn( fopen_success_val );
    fread_ExpectAnyArgsAndReturn( fread_success_val );
    fclose_ExpectAnyArgsAndReturn( fclose_fail_val );

    /* Call otaPal_GetPlatformImageState and check the result. */
    ePalImageState = otaPal_GetPlatformImageState( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalImageStateInvalid, ePalImageState );
}

/**
 * @brief This test validates that the valid states are correctly returned to
 *        the caller.
 * */
void test_OTAPAL_GetPlatformImageState_ValidStates( void )
{
    OtaPalImageState_t ePalImageState = OtaPalImageStateUnknown;
    OtaFileContext_t otaFileContext;
    FILE dummyFile;
    OtaImageState_t freadResultingState;

    /* On success, snprintf returns a positive number that is less than the amount of data requested. */
    const int snprintf_success_val = 0;
    /* On success, fopen returns a FILE address that is not null. */
    FILE * const fopen_success_val = &dummyFile;
    /* In otaPal_GetPlatformImageState, fread is always called with a 1 for the
       size parameter. So, any number other than 1 is an error. */
    const size_t fread_success_val = 1;
    /* On success, fclose returns a zero. */
    const int fclose_success_val = 0;

    /* Test the scenario where the platform state is OtaImageStateTesting. */
    freadResultingState = OtaImageStateTesting;
    /* Predefine what functions are expected to be called. */
    snprintf_ExpectAnyArgsAndReturn( snprintf_success_val );
    fopen_ExpectAnyArgsAndReturn( fopen_success_val );
    fread_ExpectAnyArgsAndReturn( fread_success_val );
    fread_ReturnThruPtr_ptr( &freadResultingState );
    fclose_ExpectAnyArgsAndReturn( fclose_success_val );
    /* Call otaPal_GetPlatformImageState and check the result. */
    ePalImageState = otaPal_GetPlatformImageState( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalImageStatePendingCommit, ePalImageState );

    /* Test the scenario where the platform state is OtaImageStateAccepted. */
    freadResultingState = OtaImageStateAccepted;
    /* Predefine what functions are expected to be called. */
    snprintf_ExpectAnyArgsAndReturn( snprintf_success_val );
    fopen_ExpectAnyArgsAndReturn( fopen_success_val );
    fread_ExpectAnyArgsAndReturn( fread_success_val );
    fread_ReturnThruPtr_ptr( &freadResultingState );
    fclose_ExpectAnyArgsAndReturn( fclose_success_val );
    /* Call otaPal_GetPlatformImageState and check the result. */
    ePalImageState = otaPal_GetPlatformImageState( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalImageStateValid, ePalImageState );

    /* Test the scenario where the platform state is an unexpected value. */
    freadResultingState = OtaLastImageState + 1;
    /* Predefine what functions are expected to be called. */
    snprintf_ExpectAnyArgsAndReturn( snprintf_success_val );
    fopen_ExpectAnyArgsAndReturn( fopen_success_val );
    fread_ExpectAnyArgsAndReturn( fread_success_val );
    fread_ReturnThruPtr_ptr( &freadResultingState );
    fclose_ExpectAnyArgsAndReturn( fclose_success_val );
    /* Call otaPal_GetPlatformImageState and check the result. */
    ePalImageState = otaPal_GetPlatformImageState( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalImageStateInvalid, ePalImageState );
}
