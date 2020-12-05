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

#include <unistd.h>
#include <sys/stat.h>
#include "unity.h"

/* For accessing OTA private functions. */
#include "ota_private.h"
#include "ota_pal_posix.h"

/* Unit test config. */
#include "ota_utest_config.h"

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

    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    result = OTA_PAL_MAIN_ERR( otaPal_Abort( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
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

    chmod( OTA_PAL_UTEST_FIRMWARE_FILE, S_IRUSR );
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;

    /* Create a file that exists with w+b mode */
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalRxFileCreateFailed, result );

    chmod( OTA_PAL_UTEST_FIRMWARE_FILE, S_IRWXU );
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/**
 * @brief Test that otaPal_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_ValidFileHandle( void )
{
    OtaPalMainStatus_t result;

    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}


/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_NullFileContext( void )
{
    int16_t bytes_written = 0;
    uint8_t data = 0xAA;

    bytes_written = otaPal_WriteBlock( NULL, 0, &data, 1 );
    TEST_ASSERT_EQUAL( OtaPalSuccess, bytes_written + 1 );
}


/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_WriteSingleByte( void )
{
    OtaPalMainStatus_t result;
    int16_t numBytesWritten;
    uint8_t data = 0xAA;

    /* TEST: Write a byte of data. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    if( TEST_PROTECT() )
    {
        numBytesWritten = otaPal_WriteBlock( &otaFile, 0, &data, 1 );
        TEST_ASSERT_EQUAL_INT( 1, numBytesWritten );
    }
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_WriteManyBlocks( void )
{
    OtaPalMainStatus_t result;
    int16_t numBytesWritten;

    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData ) * testotapalNUM_WRITE_BLOCKS;
    /* TEST: Write many bytes of data. */

    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    if( TEST_PROTECT() )
    {
        int index = 0;

        for( index = 0; index < testotapalNUM_WRITE_BLOCKS; index++ )
        {
            numBytesWritten = otaPal_WriteBlock( &otaFile, index * sizeof( dummyData ), dummyData, sizeof( dummyData ) );
            TEST_ASSERT_EQUAL_INT( sizeof( dummyData ), numBytesWritten );
        }

        /* Sufficient delay for flash write to complete. */
        /* vTaskDelay( pdMS_TO_TICKS( testotapalWRITE_BLOCKS_DELAY_MS ) ); */
    }
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_FseekError( void )
{
}

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_FwriteError( void )
{
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

/**
 * @brief Set the platform state to self-test and verify success.
 */
void test_OTAPAL_SetPlatformImageState_SelfTestImageState( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;

    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        /* Set the image state. */
        eImageState = OtaImageStateTesting;
        result = OTA_PAL_MAIN_ERR( otaPal_SetPlatformImageState( &otaFile, eImageState ) );
        TEST_ASSERT_EQUAL_INT( OtaPalSuccess, result );

        /* Verify that image state was saved correctly. */

        /* [**]All platforms need a reboot of a successfully close image in order to return
         * eOTA_PAL_ImageState_PendingCommit from otaPal_GetPlatformImageState(). So this cannot be tested.
         */
        /* For Linux platform, this can be read directly from the image state file */
        palImageState = otaPal_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStatePendingCommit, palImageState );
    }
}

/**
 * @brief Set an invalid platform image state exceeding the range and verify success.
 */
void test_OTAPAL_SetPlatformImageState_InvalidImageState( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        /* Try to set an invalid image state. */
        eImageState = ( OtaImageState_t ) ( OtaLastImageState + 1 );
        result = OTA_PAL_MAIN_ERR( otaPal_SetPlatformImageState( &otaFile, eImageState ) );
        TEST_ASSERT_EQUAL( OtaPalBadImageState, result );

        /* Read the platform image state to verify */
        /* Nothing wrote to the image state file. Ota Pal Image state remain valid */
        palImageState = otaPal_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateValid, palImageState );
    }
}

/**
 * @brief Set the image state to unknown and verify a failure.
 */
void test_OTAPAL_SetPlatformImageState_UnknownImageState( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        /* Try to set an invalid image state. */
        eImageState = OtaImageStateUnknown;
        result = OTA_PAL_MAIN_ERR( otaPal_SetPlatformImageState( &otaFile, eImageState ) );
        TEST_ASSERT_EQUAL( OtaPalBadImageState, result );

        /* Read the platform image state to verify */
        /* Nothing wrote to the image state file. Ota Pal Image state remain valid */
        palImageState = otaPal_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateValid, palImageState );
    }
}


/**
 * @brief Set platform image state to rejected and verify success.
 * We cannot test a reject failed without mocking the underlying non volatile memory.
 */
void test_OTAPAL_SetPlatformImageState_RejectImageState( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        eImageState = OtaImageStateRejected;
        result = OTA_PAL_MAIN_ERR( otaPal_SetPlatformImageState( &otaFile, eImageState ) );
        TEST_ASSERT_EQUAL_INT( OtaPalSuccess, result );

        /* Read the platform image state to verify */
        palImageState = otaPal_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateInvalid, palImageState );
    }
}

/**
 * @brief Set the platform image state to aborted.
 * We cannot test a abort failed without mocking the underlying non-volatile memory.
 */
void test_OTAPAL_SetPlatformImageState_AbortImageState( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        eImageState = OtaImageStateAborted;
        result = OTA_PAL_MAIN_ERR( otaPal_SetPlatformImageState( &otaFile, eImageState ) );
        TEST_ASSERT_EQUAL_INT( OtaPalSuccess, result );

        /* Read the platform image state to verify */
        palImageState = otaPal_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateInvalid, palImageState );
    }
}

/**
 * @brief Verify that the current image received is in the invalid state after a
 * failure to close the file because of a bad signature.
 */
void test_OTAPAL_GetPlatformImageState_InvalidImageStateFromFileCloseFailure( void )
{
    OtaPalMainStatus_t result;
    int16_t bytes_written = 0;
    Sig256_t sig = { 0 };
    OtaPalImageState_t ePalImageState = OtaPalImageStateUnknown;

    /* TEST: Invalid image returned from otaPal_GetPlatformImageState(). Using a failure to close. */
    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) OTA_PAL_UTEST_FIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        bytes_written = otaPal_WriteBlock( &otaFile,
                                           0,
                                           dummyData,
                                           sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), bytes_written );

        /* Check the signature. */
        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucInvalidSignatureLength;
        memcpy( otaFile.pSignature->data, ucInvalidSignature, ucInvalidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) OTA_PAL_UTEST_CERT_FILE;

        result = OTA_PAL_MAIN_ERR( otaPal_CloseFile( &otaFile ) );

        if( ( OtaPalBadSignerCert != result ) &&
            ( OtaPalSignatureCheckFailed != result ) &&
            ( OtaPalFileClose != result ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }

        /* The file failed to close, so it is invalid or in an unknown state. */
        ePalImageState = otaPal_GetPlatformImageState( &otaFile );
        TEST_ASSERT( ( OtaPalImageStateInvalid == ePalImageState ) ||
                     ( OtaPalImageStateUnknown == ePalImageState ) );
    }
}
