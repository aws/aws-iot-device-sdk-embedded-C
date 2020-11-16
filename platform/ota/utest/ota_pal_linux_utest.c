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
#include "ota_platform_interface.h"


/* For the prvPAL_WriteBlock_WriteManyBlocks test this is the number of blocks of
 * dummyData to write to the non-volatile memory. */
#define testotapalNUM_WRITE_BLOCKS         10

/* For the prvPAL_WriteBlock_WriteManyBlocks test this the delay time in ms following
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

/**
 * @brief Path to cert for OTA PAL test. Used to verify signature.
 * If applicable, the device must be pre-provisioned with this certificate. Please see
 * test/common/ota/test_files for the set of certificates.
 *
 * In the Windows Simultor this is the path to the certificate on your machine. The path currently
 * here is relative to the FreeRTOS root. If you are debugging locally, Visual Studio may have
 * your path set as the project directory. In that case this can be changed to:
 *
 * #define otatestpalCERTIFICATE_FILE  "..\\..\\..\\..\\..\\libraries\\freertos_plus\\aws\\ota\\test\\test_files\\ecdsa-sha256-signer.crt.pem"
 */
#define otatestpalCERTIFICATE_FILE    "../../../platform/ota/utest/test_files/ecdsa-sha256-signer.crt.pem"

/**
 * @brief Some devices have a hard-coded name for the firmware image to boot.
 */
#define otatestpalFIRMWARE_FILE       "dummy.bin"


/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
    /* Always reset the OTA file context before each test. */
    memset( &otaFile, 0, sizeof( otaFile ) );
}

void tearDown( void )
{
    OtaErr_t result;

    /* We want to abort the OTA file after every test. This closes the OtaFile. */
    result = prvPAL_Abort( &otaFile );

    if( OTA_ERR_NONE != result )
    {
        LogError( ( "Error aborting otaFile with code: %d", result ) );
    }

    unlink( "PlatformImageState.txt" );
}

/* ========================================================================== */

/**
 * @brief Test that prvPAL_Abort will return correct result code.
 */
void test_OTAPAL_Abort_NullFileContext( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    result = prvPAL_Abort( NULL );

    TEST_ASSERT_EQUAL( OTA_ERR_FILE_ABORT, result );
}


/**
 * @brief Test that prvPAL_Abort will return correct result code.
 */
void test_OTAPAL_Abort_NullFileHandle( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaFile.pFile = NULL;
    result = prvPAL_Abort( &otaFile );

    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
}

/**
 * @brief Test that prvPAL_Abort will return correct result code.
 */
/* void test_OTAPAL_Abort_InvalidFileHandle( void ) */
/* { */
/*     OtaErr_t result = OTA_ERR_UNINITIALIZED; */

/*     otaFile.pFilePath = ( uint8_t *) otatestpalFIRMWARE_FILE; */
/*     result = prvPAL_CreateFileForRx( &otaFile) ; */
/*     TEST_ASSERT_EQUAL( OTA_ERR_NONE, result ); */

/*     otaFile.pFile += 8; */
/*     result = prvPAL_Abort( &otaFile ); */
/*     TEST_ASSERT_EQUAL( OTA_ERR_FILE_ABORT, ( result & OTA_MAIN_ERR_MASK)); */
/* } */

/**
 * @brief Test that prvPAL_Abort will return correct result code.
 */
void test_OTAPAL_Abort_ValidFileHandle( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    result = prvPAL_Abort( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
}

/**
 * @brief Test that prvPAL_Abort will return correct result code.
 */
void test_OTAPAL_Abort_NonExistentFile( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaFile.pFilePath = ( uint8_t * ) ( "nonexistingfile.bin" );
    result = prvPAL_Abort( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, ( result & OTA_MAIN_ERR_MASK ) );
}

/**
 * @brief Test that prvPAL_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_NullFileContext( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    result = prvPAL_CreateFileForRx( NULL );
    TEST_ASSERT_EQUAL( OTA_ERR_RX_FILE_CREATE_FAILED, result );
}


/**
 * @brief Test that prvPAL_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_NullFilePath( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaFile.pFilePath = NULL;
    result = prvPAL_CreateFileForRx( &otaFile );

    TEST_ASSERT_EQUAL( OTA_ERR_RX_FILE_CREATE_FAILED, result );
}

/**
 * @brief Test that prvPAL_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_FailedToCreateFile( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    FILE * existingFile = fopen( otatestpalFIRMWARE_FILE, "r" );

    chmod( otatestpalFIRMWARE_FILE, S_IRUSR );
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;

    /* Create a file that exists with w+b mode */
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_RX_FILE_CREATE_FAILED, ( result & OTA_MAIN_ERR_MASK ) );

    chmod( otatestpalFIRMWARE_FILE, S_IRWXU );
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, ( result & OTA_MAIN_ERR_MASK ) );
}

/**
 * @brief Test that prvPAL_CreateFileForRx will return correct result code.
 */
void test_OTAPAL_CreateFileForRx_ValidFileHandle( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
}


/**
 * @brief Test that prvPAL_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_NullFileContext( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    uint8_t data = 0xAA;

    result = prvPAL_WriteBlock( NULL, 0, &data, 1 );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result + 1 );
}


/**
 * @brief Test that prvPAL_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_WriteSingleByte( void )
{
    OtaErr_t result;
    int16_t numBytesWritten;
    uint8_t data = 0xAA;

    /* TEST: Write a byte of data. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    if( TEST_PROTECT() )
    {
        numBytesWritten = prvPAL_WriteBlock( &otaFile, 0, &data, 1 );
        TEST_ASSERT_EQUAL_INT( 1, numBytesWritten );
    }
}

/**
 * @brief Test that prvPAL_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_WriteManyBlocks( void )
{
    OtaErr_t result;
    int16_t numBytesWritten;

    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData ) * testotapalNUM_WRITE_BLOCKS;
    /* TEST: Write many bytes of data. */

    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    if( TEST_PROTECT() )
    {
        int index = 0;

        for( index = 0; index < testotapalNUM_WRITE_BLOCKS; index++ )
        {
            numBytesWritten = prvPAL_WriteBlock( &otaFile, index * sizeof( dummyData ), dummyData, sizeof( dummyData ) );
            TEST_ASSERT_EQUAL_INT( sizeof( dummyData ), numBytesWritten );
        }

        /* Sufficient delay for flash write to complete. */
        /* vTaskDelay( pdMS_TO_TICKS( testotapalWRITE_BLOCKS_DELAY_MS ) ); */
    }
}

/**
 * @brief Test that prvPAL_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_FseekError( void )
{
}

/**
 * @brief Test that prvPAL_WriteBlock will return correct result code.
 */
void test_OTAPAL_WriteBlock_FwriteError( void )
{
}

void test_OTAPAL_CloseFile_ValidSignature( void )
{
    OtaErr_t result;
    Sig256_t sig = { 0 };

    /* We use a dummy file name here because closing the system designated bootable
     * image with content that is not runnable may cause issues. */
    otaFile.pFilePath = ( uint8_t * ) ( "test_happy_path_image.bin" );
    otaFile.fileSize = sizeof( dummyData );
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucValidSignatureLength;
        memcpy( otaFile.pSignature->data, ucValidSignature, ucValidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) otatestpalCERTIFICATE_FILE;

        result = prvPAL_CloseFile( &otaFile );
        TEST_ASSERT_EQUAL_INT( OTA_ERR_NONE, result );
    }
}


/**
 * @brief Call prvPAL_CloseFile with an invalid signature in the file context.
 * The close is called after we have a written a block of dummy data to the file.
 * Verify the correct OTA Agent level error code is returned from prvPAL_CloseFile.
 */
void test_OTAPAL_CloseFile_InvalidSignatureBlockWritten( void )
{
    OtaErr_t result;
    Sig256_t sig = { 0 };

    /* Create a local file using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        /* Fill out an incorrect signature. */
        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucInvalidSignatureLength;
        memcpy( otaFile.pSignature->data, ucInvalidSignature, ucInvalidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) otatestpalCERTIFICATE_FILE;

        /* Try to close the file. */
        result = prvPAL_CloseFile( &otaFile );

        if( ( OTA_ERR_BAD_SIGNER_CERT != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_SIGNATURE_CHECK_FAILED != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_FILE_CLOSE != ( result & OTA_MAIN_ERR_MASK ) ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }
    }
}

/**
 * @brief Call prvPAL_CloseFile with an invalid signature in the file context.
 * The close is called when no blocks have been written to the file.
 * Verify the correct OTA Agent level error code is returned from prvPAL_CloseFile.
 */
void test_OTAPAL_CloseFile_InvalidSignatureNoBlockWritten( void )
{
    OtaErr_t result;
    Sig256_t sig = { 0 };

    /* Create a local file using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* Fill out an incorrect signature. */
    otaFile.pSignature = &sig;
    otaFile.pSignature->size = ucInvalidSignatureLength;
    memcpy( otaFile.pSignature->data, ucInvalidSignature, ucInvalidSignatureLength );
    otaFile.pCertFilepath = ( uint8_t * ) otatestpalCERTIFICATE_FILE;

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Try to close the file. */
        result = prvPAL_CloseFile( &otaFile );

        if( ( OTA_ERR_BAD_SIGNER_CERT != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_SIGNATURE_CHECK_FAILED != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_FILE_CLOSE != ( result & OTA_MAIN_ERR_MASK ) ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }
    }
}

/**
 * @brief Call prvPAL_CloseFile with a signature verification certificate path does
 * not exist in the system. Verify the correct OTA Agent level error code is returned
 * from prvPAL_CloseFile.
 *
 * @note This test is only valid if your device uses a file system in your non-volatile memory.
 * Some devices may revert to using aws_codesigner_certificate.h if a file is not found, but
 * that option is not being enforced.
 */
void test_OTAPAL_CloseFile_NonexistingCodeSignerCertificate( void )
{
    OtaErr_t result;
    Sig256_t sig = { 0 };

    memset( &otaFile, 0, sizeof( otaFile ) );

    /* Create a local file using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails somewhere here. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        /* Check the signature (not expected to be valid in this case). */
        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucValidSignatureLength;
        memcpy( otaFile.pSignature->data, ucValidSignature, ucValidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) ( "nonexistingfile.crt" );

        result = prvPAL_CloseFile( &otaFile );

        if( ( OTA_ERR_BAD_SIGNER_CERT != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_SIGNATURE_CHECK_FAILED != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_FILE_CLOSE != ( result & OTA_MAIN_ERR_MASK ) ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }
    }
}

/**
 * @brief Test that prvPAL_ResetDevice will return correct result code.
 */
void test_OTAPAL_ResetDevice_NullFileContext( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    result = prvPAL_ResetDevice( NULL );
    TEST_ASSERT_EQUAL( OTA_ERR_NULL_FILE_PTR, result );
}

/**
 * @brief Test that prvPAL_WriteBlock will return correct result code.
 */
void test_OTAPAL_ActivateNewImage_NullFileContext( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    result = prvPAL_ActivateNewImage( NULL );
    TEST_ASSERT_EQUAL( OTA_ERR_NULL_FILE_PTR, result );
}

/**
 * @brief Set the platform state to self-test and verify success.
 */
void test_OTAPAL_SetPlatformImageState_SelfTestImageState( void )
{
    OtaErr_t result;

    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        /* Set the image state. */
        eImageState = OtaImageStateTesting;
        result = prvPAL_SetPlatformImageState( &otaFile, eImageState );
        TEST_ASSERT_EQUAL_INT( OTA_ERR_NONE, result );

        /* Verify that image state was saved correctly. */

        /* [**]All platforms need a reboot of a successfully close image in order to return
         * eOTA_PAL_ImageState_PendingCommit from prvPAL_GetPlatformImageState(). So this cannot be tested.
         */
        /* For Linux platform, this can be read directly from the image state file */
        palImageState = prvPAL_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStatePendingCommit, palImageState );
    }
}

/**
 * @brief Set an invalid platform image state exceeding the range and verify success.
 */
void test_OTAPAL_SetPlatformImageState_InvalidImageState( void )
{
    OtaErr_t result;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        /* Try to set an invalid image state. */
        eImageState = ( OtaImageState_t ) ( OtaLastImageState + 1 );
        result = prvPAL_SetPlatformImageState( &otaFile, eImageState );
        TEST_ASSERT_EQUAL( OTA_ERR_BAD_IMAGE_STATE, ( result & OTA_MAIN_ERR_MASK ) );

        /* Read the platform image state to verify */
        /* Nothing wrote to the image state file. Ota Pal Image state remain valid */
        palImageState = prvPAL_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateValid, palImageState );
    }
}

/**
 * @brief Set the image state to unknown and verify a failure.
 */
void test_OTAPAL_SetPlatformImageState_UnknownImageState( void )
{
    OtaErr_t result;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        /* Try to set an invalid image state. */
        eImageState = OtaImageStateUnknown;
        result = prvPAL_SetPlatformImageState( &otaFile, eImageState );
        TEST_ASSERT_EQUAL( OTA_ERR_BAD_IMAGE_STATE, ( result & OTA_MAIN_ERR_MASK ) );

        /* Read the platform image state to verify */
        /* Nothing wrote to the image state file. Ota Pal Image state remain valid */
        palImageState = prvPAL_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateValid, palImageState );
    }
}


/**
 * @brief Set platform image state to rejected and verify success.
 * We cannot test a reject failed without mocking the underlying non volatile memory.
 */
void test_OTAPAL_SetPlatformImageState_RejectImageState( void )
{
    OtaErr_t result;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        eImageState = OtaImageStateRejected;
        result = prvPAL_SetPlatformImageState( &otaFile, eImageState );
        TEST_ASSERT_EQUAL_INT( OTA_ERR_NONE, ( result & OTA_MAIN_ERR_MASK ) );

        /* Read the platform image state to verify */
        palImageState = prvPAL_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateInvalid, palImageState );
    }
}

/**
 * @brief Set the platform image state to aborted.
 * We cannot test a abort failed without mocking the underlying non-volatile memory.
 */
void test_OTAPAL_SetPlatformImageState_AbortImageState( void )
{
    OtaErr_t result;
    OtaImageState_t eImageState = OtaImageStateUnknown;
    OtaPalImageState_t palImageState = OtaPalImageStateUnknown;

    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        eImageState = OtaImageStateAborted;
        result = prvPAL_SetPlatformImageState( &otaFile, eImageState );
        TEST_ASSERT_EQUAL_INT( OTA_ERR_NONE, ( result & OTA_MAIN_ERR_MASK ) );

        /* Read the platform image state to verify */
        palImageState = prvPAL_GetPlatformImageState( &otaFile );
        TEST_ASSERT_EQUAL_INT( OtaPalImageStateInvalid, palImageState );
    }
}

/**
 * @brief Verify that the current image received is in the invalid state after a
 * failure to close the file because of a bad signature.
 */
void test_OTAPAL_GetPlatformImageState_InvalidImageStateFromFileCloseFailure( void )
{
    OtaErr_t result;
    Sig256_t sig = { 0 };
    OtaPalImageState_t ePalImageState = OtaPalImageStateUnknown;

    /* TEST: Invalid image returned from prvPAL_GetPlatformImageState(). Using a failure to close. */
    /* Create a local file again using the PAL. */
    otaFile.pFilePath = ( uint8_t * ) otatestpalFIRMWARE_FILE;
    otaFile.fileSize = sizeof( dummyData );

    result = prvPAL_CreateFileForRx( &otaFile );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* We still want to close the file if the test fails. */
    if( TEST_PROTECT() )
    {
        /* Write data to the file. */
        result = prvPAL_WriteBlock( &otaFile,
                                    0,
                                    dummyData,
                                    sizeof( dummyData ) );
        TEST_ASSERT_EQUAL( sizeof( dummyData ), result );

        /* Check the signature. */
        otaFile.pSignature = &sig;
        otaFile.pSignature->size = ucInvalidSignatureLength;
        memcpy( otaFile.pSignature->data, ucInvalidSignature, ucInvalidSignatureLength );
        otaFile.pCertFilepath = ( uint8_t * ) otatestpalCERTIFICATE_FILE;

        result = prvPAL_CloseFile( &otaFile );

        if( ( OTA_ERR_BAD_SIGNER_CERT != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_SIGNATURE_CHECK_FAILED != ( result & OTA_MAIN_ERR_MASK ) ) &&
            ( OTA_ERR_FILE_CLOSE != ( result & OTA_MAIN_ERR_MASK ) ) )
        {
            TEST_ASSERT_TRUE( 0 );
        }

        /* The file failed to close, so it is invalid or in an unknown state. */
        ePalImageState = prvPAL_GetPlatformImageState( &otaFile );
        TEST_ASSERT( ( OtaPalImageStateInvalid == ePalImageState ) ||
                     ( OtaPalImageStateUnknown == ePalImageState ) );
    }
}
