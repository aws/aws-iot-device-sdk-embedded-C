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
#include "mock_openssl_api.h"

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

    unlink( "PlatformImageState.txt" );
}

/* ==========================   HELPER FUNCTIONS   ========================== */
typedef enum
{
    none_fn = 0,
    BIO_s_file_fn,
    BIO_new_fn,
    BIO_s_mem_fn,
    BIO_puts_fn,
    BIO_free_all_fn,
    BIO_read_filename_fn,
    PEM_read_bio_X509_fn,
    X509_get_pubkey_fn,
    X509_free_fn,
    EVP_MD_CTX_new_fn,
    EVP_DigestVerifyInit_fn,
    EVP_DigestVerifyUpdate_fn,
    EVP_DigestVerifyFinal_fn,
    EVP_MD_CTX_free_fn,
    EVP_PKEY_free_fn,
    EVP_sha256_fn,
    OPENSSL_malloc_fn,
    CRYPTO_free_fn,
    fopen_fn,
    fclose_fn,
    snprintf_fn,
    fread_fn,
    fseek_alias_fn,
    fwrite_alias_fn
} MockFunctionNames_t;

static void OTA_PAL_FailSingleMock_Except_fread(MockFunctionNames_t funcToFail, OtaImageState_t *pFreadStateToSet);
static void OTA_PAL_FailSingleMock_openssl_BIO( MockFunctionNames_t funcToFail );
static void OTA_PAL_FailSingleMock_openssl_X509( MockFunctionNames_t funcToFail );
static void OTA_PAL_FailSingleMock_openssl_EVP( MockFunctionNames_t funcToFail );
static void OTA_PAL_FailSingleMock_openssl_crypto( MockFunctionNames_t funcToFail );
static void OTA_PAL_FailSingleMock_stdio( MockFunctionNames_t funcToFail, OtaImageState_t* pFreadStateToSet );
static void OTA_PAL_FailSingleMock( MockFunctionNames_t funcToFail, OtaImageState_t* pFreadStateToSet );

static void OTA_PAL_FailSingleMock_Except_fread(MockFunctionNames_t funcToFail, OtaImageState_t *pFreadStateToSet)
{
    const size_t fread_failure = 0;
    /* When fread is being called in this case, it is looping until there is
    no more data. Setting fread to fail prevents us from getting stuck in
    the loops. */
    OTA_PAL_FailSingleMock_stdio(funcToFail, pFreadStateToSet );

    fread_IgnoreAndReturn( fread_failure );
    fread_ReturnThruPtr_ptr( pFreadStateToSet );

    OTA_PAL_FailSingleMock_openssl_BIO( funcToFail );
    OTA_PAL_FailSingleMock_openssl_X509( funcToFail );
    OTA_PAL_FailSingleMock_openssl_crypto( funcToFail );
    OTA_PAL_FailSingleMock_openssl_EVP( funcToFail );
}

static void OTA_PAL_FailSingleMock_openssl_BIO( MockFunctionNames_t funcToFail )
{
    /*
     * Define success and failure return values for OpenSSL BIO.h mocks.
     */
    static BIO_METHOD dummyBioMethod;
    static BIO dummyBIO;
    /* BIO_s_file_fn: Has no documented failure returns. It always returns a
     * valid "BIO_METHOD *". */
    BIO_METHOD* BIO_s_file_return;
    /* BIO_new_fn: Returns a newly created BIO or NULL if the call fails. */
    BIO* BIO_new_success = &dummyBIO;
    BIO* BIO_new_failure = NULL;
    BIO* BIO_new_return;
    /* BIO_s_mem_fn: Has no documented failure returns. It always returns
     * a valid "BIO_METHOD *". */
    BIO_METHOD* BIO_s_mem_return;
    /* BIO_puts_fn: Returns either the amount of data successfully written
     * (if the return value is positive) or that no data was succesfully
     * written if the result is 0 or -1. */
    int BIO_puts_success = 1;
    int BIO_puts_failure = 0;
    int BIO_puts_return;
    /* BIO_free_all_fn: Does not return anything. */
    /* BIO_read_filename_fn: Calls BIO_ctrl indirectly. BIO_ctrl
     * returns 1 for success or 0 for failure. */
    long BIO_read_filename_fn_success = 1;
    long BIO_read_filename_fn_failure = 0;
    long BIO_read_filename_fn_return;

    /*
     * Set the return value for the mock ( if any ) that matches the input. Set
     * the rest of the mock functions to return the success value when called.
     */
    BIO_s_file_return = &dummyBioMethod;
    BIO_s_file_IgnoreAndReturn(BIO_s_file_return);

    BIO_new_return = ( funcToFail == BIO_new_fn ) ? BIO_new_failure : BIO_new_success;
    BIO_new_IgnoreAndReturn( BIO_new_return );

    BIO_s_mem_return = &dummyBioMethod;
    BIO_s_mem_IgnoreAndReturn( BIO_s_mem_return );

    BIO_puts_return = ( funcToFail == BIO_puts_fn ) ? BIO_puts_failure : BIO_puts_success;
    BIO_puts_IgnoreAndReturn( BIO_puts_return );

    BIO_free_all_Ignore();

    BIO_read_filename_fn_return = ( funcToFail == BIO_read_filename_fn ) ? BIO_read_filename_fn_failure : BIO_read_filename_fn_success;
    BIO_ctrl_IgnoreAndReturn( BIO_read_filename_fn_return );
}

static void OTA_PAL_FailSingleMock_openssl_X509( MockFunctionNames_t funcToFail )
{
    /*
     * Define success and failure return values for OpenSSL X509.h mocks.
     */
    static X509 dummyX509;
    static EVP_PKEY dummyEVP_PKEY;
    /* PEM_read_bio_X509_fn: Returns a valid "X509 *" on success and NULL on error. */
    X509* PEM_read_bio_X509_success = &dummyX509;
    X509* PEM_read_bio_X509_failure = NULL;
    X509* PEM_read_bio_X509_return;
    /* X509_get_pubkey_fn: Returns EVP_PKEY* on success and NULL on error. */
    EVP_PKEY* X509_get_pubkey_success = &dummyEVP_PKEY;
    EVP_PKEY* X509_get_pubkey_failure = NULL;
    EVP_PKEY* X509_get_pubkey_return;
    /* X509_free_fn: Doesn't return anything. */

    /*
     * Set the return value for the mock ( if any ) that matches the input. Set
     * the rest of the mock functions to return the success value when called.
     */
    PEM_read_bio_X509_return = ( funcToFail == PEM_read_bio_X509_fn ) ? PEM_read_bio_X509_failure : PEM_read_bio_X509_success;
    PEM_read_bio_X509_IgnoreAndReturn( PEM_read_bio_X509_return );

    X509_get_pubkey_return = ( funcToFail == X509_get_pubkey_fn ) ? X509_get_pubkey_failure : X509_get_pubkey_success;
    X509_get_pubkey_IgnoreAndReturn( X509_get_pubkey_return );

    X509_free_Ignore();
}

static void OTA_PAL_FailSingleMock_openssl_EVP( MockFunctionNames_t funcToFail )
{
    static EVP_MD_CTX dummyEVP_MD_CTX;
    static EVP_MD dummyEVP_MD;
    /* EVP_MD_CTX_new_fn: Has no documented failure returns. Allocates and returns a valid digest context. */
    EVP_MD_CTX* EVP_MD_CTX_new_return;
    /* EVP_DigestVerifyInit_fn: Return 1 for success and 0 for failure. */
    int EVP_DigestVerifyInit_success = 1;
    int EVP_DigestVerifyInit_failure = 0;
    int EVP_DigestVerifyInit_return;
    /* EVP_DigestVerifyUpdate_fn: Return 1 for success and 0 for failure. */
    int EVP_DigestVerifyUpdate_success = 1;
    int EVP_DigestVerifyUpdate_failure = 0;
    int EVP_DigestVerifyUpdate_return;
    /* EVP_DigestVerifyFinal_fn: Return 1 for success; any other value indicates a failure. */
    int EVP_DigestVerifyFinal_success = 1;
    int EVP_DigestVerifyFinal_failure = -1;
    int EVP_DigestVerifyFinal_return;
    /* EVP_MD_CTX_free_fn: No return. */
    /* EVP_PKEY_free_fn: No return. */

    EVP_MD_CTX_new_return = &dummyEVP_MD_CTX;
    EVP_MD_CTX_new_IgnoreAndReturn( EVP_MD_CTX_new_return );

    EVP_DigestVerifyInit_return = ( funcToFail == EVP_DigestVerifyInit_fn ) ? EVP_DigestVerifyInit_failure : EVP_DigestVerifyInit_success;
    EVP_DigestVerifyInit_IgnoreAndReturn( EVP_DigestVerifyInit_return );

    EVP_DigestVerifyUpdate_return = ( funcToFail == EVP_DigestVerifyUpdate_fn ) ? EVP_DigestVerifyUpdate_failure : EVP_DigestVerifyUpdate_success;
    EVP_DigestUpdate_IgnoreAndReturn( EVP_DigestVerifyUpdate_return );

    EVP_DigestVerifyFinal_return = ( funcToFail == EVP_DigestVerifyFinal_fn ) ? EVP_DigestVerifyFinal_failure : EVP_DigestVerifyFinal_success;
    EVP_DigestVerifyFinal_IgnoreAndReturn( EVP_DigestVerifyFinal_return );

    EVP_MD_CTX_free_Ignore();

    EVP_PKEY_free_Ignore();

    EVP_sha256_IgnoreAndReturn( &dummyEVP_MD ); //TODO: Add variables and descriptions and other conditions 
}

static void OTA_PAL_FailSingleMock_openssl_crypto( MockFunctionNames_t funcToFail )
{
    int mockVariable;

    /* OPENSSL_malloc is a macro define for CRYPTO_malloc. */
    void* OPENSSL_malloc_success = &mockVariable;
    void* OPENSSL_malloc_failure = NULL;
    void* OPENSSL_malloc_return;

    OPENSSL_malloc_return = ( funcToFail == OPENSSL_malloc_fn ) ? OPENSSL_malloc_failure : OPENSSL_malloc_success;
    CRYPTO_malloc_StopIgnore();
    CRYPTO_malloc_IgnoreAndReturn( OPENSSL_malloc_return );
    /* CRYPTO_free_fn: Has no return value. */
    CRYPTO_free_Ignore();
}

/**
 * @brief Helper function specify a single point of failure for
 * otaPal_SetPlatformImageState. This needs to be updated each time a mocked
 * function is added or removed to otaPal_SetPlatformImageState. 
 * 
 * Remark: This function assumes specific values for the success and failure of the functions. */
static void OTA_PAL_FailSingleMock_stdio( MockFunctionNames_t funcToFail, OtaImageState_t* pFreadStateToSet )
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

static void OTA_PAL_FailSingleMock( MockFunctionNames_t funcToFail, OtaImageState_t* pFreadStateToSet )
{
    OTA_PAL_FailSingleMock_stdio( funcToFail, pFreadStateToSet );
    OTA_PAL_FailSingleMock_openssl_BIO( funcToFail );
    OTA_PAL_FailSingleMock_openssl_X509( funcToFail );
    OTA_PAL_FailSingleMock_openssl_crypto( funcToFail );
    OTA_PAL_FailSingleMock_openssl_EVP( funcToFail );
}

/* ======================   OTA PAL ABORT UNIT TESTS   ====================== */

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

/* ===================   OTA PAL CREATE FILE UNIT TESTS   =================== */

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
 * @brief Test that otaPal_CreateFileForRx will handle the two types of
 * potential paths.
 */
void test_OTAPAL_CreateFileForRx_PathTypes( void )
{
    OtaPalMainStatus_t result;
    FILE placeholder_file;

    /* Test for a leading forward slash in the path. */
    otaFile.pFilePath = ( uint8_t * ) "/placeholder_path";
    fopen_ExpectAnyArgsAndReturn( &placeholder_file );
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );

    /* Test for no leading forward slash in the path. */
    otaFile.pFilePath = ( uint8_t * ) "placeholder_path";
    fopen_ExpectAnyArgsAndReturn( &placeholder_file );
    result = OTA_PAL_MAIN_ERR( otaPal_CreateFileForRx( &otaFile ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/* ===================   OTA PAL CLOSE FILE UNIT TESTS   ==================== */

void test_OTAPAL_CloseFile_NullInput( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    OTA_PAL_FailSingleMock_Except_fread( fread_fn, &expectedImageState );

    /* NULL file context. */
    result = otaPal_CloseFile( NULL );
    TEST_ASSERT_EQUAL( OtaPalFileClose, OTA_PAL_MAIN_ERR( result ) );

    /* NULL signature input. */
    otaFileContext.pSignature = NULL;
    otaFileContext.pFile = &dummyFile;
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSignatureCheckFailed, OTA_PAL_MAIN_ERR( result ) );

    /* NULL file input */
    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = NULL;
    /* NULL signature input. */
    OTA_PAL_FailSingleMock_Except_fread( fread_fn, &expectedImageState );
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSignatureCheckFailed, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_HappyPath( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;
    /* When fread is being called in this case, it is looping until there is
       no more data. Setting fread to fail prevents us from getting stuck in
       the loops. */
    OTA_PAL_FailSingleMock( fread_fn, &expectedImageState );
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_OpenSSL_failures( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    OTA_PAL_FailSingleMock_Except_fread( BIO_puts_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );

    /* Test OpenSSL/X509.h functions failing. */
    otaFileContext.pFile = &dummyFile;
    OTA_PAL_FailSingleMock_Except_fread( PEM_read_bio_X509_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalBadSignerCert, OTA_PAL_MAIN_ERR( result ) );

    otaFileContext.pFile = &dummyFile;
    OTA_PAL_FailSingleMock_Except_fread( X509_get_pubkey_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );

    /* Test fclose failing. */
    otaFileContext.pFile = &dummyFile;
    OTA_PAL_FailSingleMock_Except_fread( fclose_fn , &expectedImageState);
    /* Just want the first fclose to fail. */
    fclose_StopIgnore();
    fclose_ExpectAnyArgsAndReturn( EOF );
    fclose_IgnoreAndReturn( 0 );
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalFileClose, OTA_PAL_MAIN_ERR( result ) );

    /* Test OPENSSL_malloc failing. */
    otaFileContext.pFile = &dummyFile;
    OTA_PAL_FailSingleMock_Except_fread( OPENSSL_malloc_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalOutOfMemory, OTA_PAL_MAIN_ERR( result ) );


}

void test_OTAPAL_CloseFile_EVP_DigestVerifyFinal_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    /* Test fseek failing. */
    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    OTA_PAL_FailSingleMock_Except_fread( EVP_DigestVerifyFinal_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSignatureCheckFailed, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_fseek_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    /* Test fseek failing. */
    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    OTA_PAL_FailSingleMock_Except_fread( fseek_alias_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_fread_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    /* Test fread pass then fail. */
    OTA_PAL_FailSingleMock( none_fn , &expectedImageState);
    fread_StopIgnore();
    fread_ExpectAnyArgsAndReturn( 1 );
    fread_ExpectAnyArgsAndReturn( 0 );
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_BIO_new( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;
    BIO dummyBIO;

    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    /* Test OpenSSL/bio.h functions failing. */
    OTA_PAL_FailSingleMock_Except_fread( none_fn , &expectedImageState);
    BIO_new_StopIgnore();
    BIO_ctrl_StopIgnore();
    BIO_new_ExpectAnyArgsAndReturn( &dummyBIO );
    BIO_ctrl_ExpectAnyArgsAndReturn( 0 );
    BIO_new_ExpectAnyArgsAndReturn( NULL );
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalBadSignerCert, OTA_PAL_MAIN_ERR( result ) );


    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;
    OTA_PAL_FailSingleMock_Except_fread( BIO_new_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalBadSignerCert, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_BIO_read_filename_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    OTA_PAL_FailSingleMock_Except_fread( BIO_read_filename_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSuccess, OTA_PAL_MAIN_ERR( result ) );
}

void test_OTAPAL_CloseFile_EVP_DigestVerifyInit_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    Sig256_t dummySig;
    OtaImageState_t expectedImageState = OtaImageStateTesting;
    FILE dummyFile;

    otaFileContext.pSignature = &dummySig;
    otaFileContext.pFile = &dummyFile;

    OTA_PAL_FailSingleMock_Except_fread( EVP_DigestVerifyInit_fn , &expectedImageState);
    result = otaPal_CloseFile( &otaFileContext );
    TEST_ASSERT_EQUAL( OtaPalSignatureCheckFailed, OTA_PAL_MAIN_ERR( result ) );
}

/* ===================   OTA PAL WRITE BLOCK UNIT TESTS   =================== */

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
    for( index = 0; index < ( sizeof(pData) / sizeof(pData[0]) ); index++ )
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

/* ===============   OTA PAL ACTIVATE NEW IMAGE UNIT TESTS   ================ */

/**
 * @brief Test that otaPal_WriteBlock will return correct result code.
 */
void test_OTAPAL_ActivateNewImage_NullFileContext( void )
{
    OtaPalMainStatus_t result;

    result = OTA_PAL_MAIN_ERR( otaPal_ActivateNewImage( NULL ) );
    TEST_ASSERT_EQUAL( OtaPalSuccess, result );
}

/* ==================   OTA PAL RESET DEVICE UNIT TESTS   =================== */

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

/* ============   OTA PAL SET PLATFORM IMAGE STATE UNIT TESTS   ============= */

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

    OTA_PAL_FailSingleMock_stdio( none_fn, NULL );
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

    OTA_PAL_FailSingleMock_stdio( fopen_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalBadImageState, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles fwrite failing.
 */
void test_OTAPAL_SetPlatformImageState_fwrite_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock_stdio( fwrite_alias_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalBadImageState, OTA_PAL_MAIN_ERR( result ) );
}

/**
 * @brief Test otaPal_SetPlatformImageState correctly handles fclose failing.
 */
void test_OTAPAL_SetPlatformImageState_fclose_fail( void )
{
    OtaPalStatus_t result;
    OtaFileContext_t otaFileContext;
    OtaImageState_t validState = OtaImageStateTesting;

    OTA_PAL_FailSingleMock_stdio( fclose_fn, NULL );
    result = otaPal_SetPlatformImageState( &otaFileContext, validState );
    TEST_ASSERT_EQUAL( OtaPalBadImageState, OTA_PAL_MAIN_ERR( result ) );
}

/* ============   OTA PAL GET PLATFORM IMAGE STATE UNIT TESTS   ============= */

/**
 * @brief Verify that otaPal_GetPlatformImageState correctly handles a fopen
 *        failure. This test assumes that all other function calls return
 *        success.
 * */
void test_OTAPAL_GetPlatformImageState_fopen_fails( void )
{
    OtaPalImageState_t ePalImageState;
    OtaFileContext_t otaFileContext;

    OTA_PAL_FailSingleMock_stdio( fopen_fn, NULL );
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

    OTA_PAL_FailSingleMock_stdio( fread_fn , NULL );
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
