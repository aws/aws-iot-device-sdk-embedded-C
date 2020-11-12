/*
 * AWS IoT Device SDK for Embedded C V202011.00
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

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* PKCS includes. */
#include "core_pki_utils.h"
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"
#include "core_test_pkcs11_config.h"

/* Loggign includes. */
#include "logging_levels.h"
#include "logging_stack.h"

/* Test includes. */
#include "unity.h"

/* mbedTLS includes. */
#include "mbedtls/sha256.h"
#include "mbedtls/pk.h"
#include "mbedtls/pk_internal.h"
#include "mbedtls/oid.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/entropy_poll.h"
#include "mbedtls/x509_crt.h"

/* Length parameters for importing RSA-2048 private keys. */
#define MODULUS_LENGTH              pkcs11RSA_2048_MODULUS_BITS / 8
#define E_LENGTH                    3
#define D_LENGTH                    pkcs11RSA_2048_MODULUS_BITS / 8
#define PRIME_1_LENGTH              128
#define PRIME_2_LENGTH              128
#define EXPONENT_1_LENGTH           128
#define EXPONENT_2_LENGTH           128
#define COEFFICIENT_LENGTH          128
#define PUB_EXP_LENGTH              3

#define CERTIFICATE_VALUE_LENGTH    949
#define pkcstestRAND_BUFFER_SIZE    10
#define EC_PARAMS_LENGTH            10
#define EC_D_LENGTH                 32


typedef struct RsaParams_t
{
    CK_BYTE modulus[ MODULUS_LENGTH + 1 ];
    CK_BYTE e[ E_LENGTH + 1 ];
    CK_BYTE d[ D_LENGTH + 1 ];
    CK_BYTE prime1[ PRIME_1_LENGTH + 1 ];
    CK_BYTE prime2[ PRIME_2_LENGTH + 1 ];
    CK_BYTE exponent1[ EXPONENT_1_LENGTH + 1 ];
    CK_BYTE exponent2[ EXPONENT_2_LENGTH + 1 ];
    CK_BYTE coefficient[ COEFFICIENT_LENGTH + 1 ];
} RsaParams_t;

/* PKCS #11 Globals.
 * These are used to reduce setup and tear down calls, and to
 * prevent memory leaks in the case of TEST_PROTECT() actions being triggered. */
CK_SESSION_HANDLE xGlobalSession = 0;
CK_FUNCTION_LIST_PTR pxGlobalFunctionList = NULL_PTR;
CK_SLOT_ID xGlobalSlotId = 0;
CK_MECHANISM_TYPE xGlobalMechanismType = 0;

/* Model Based Tests (MBT) test group variables. */
CK_OBJECT_HANDLE xGlobalPublicKeyHandle = 0;
CK_OBJECT_HANDLE xGlobalPrivateKeyHandle = 0;
CK_BBOOL xGlobalCkTrue = CK_TRUE;
CK_BBOOL xGlobalCkFalse = CK_FALSE;

/* PKCS #11 Global Data Containers. */
CK_BYTE rsaHashedMessage[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
CK_BYTE ecdsaSignature[ pkcs11RSA_2048_SIGNATURE_LENGTH ] = { 0x00 };
CK_BYTE ecdsaHashedMessage[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xab };

/*-----------------------------------------------------------*/

/* Import the specified ECDSA private key into storage. */
static CK_RV prvProvisionPrivateECKey( CK_SESSION_HANDLE xSession,
                                       uint8_t * pucLabel,
                                       CK_OBJECT_HANDLE_PTR pxObjectHandle,
                                       mbedtls_pk_context * pxMbedPkContext );

/* Import the specified RSA private key into storage. */
static CK_RV prvProvisionPrivateRSAKey( CK_SESSION_HANDLE xSession,
                                        uint8_t * pucLabel,
                                        CK_OBJECT_HANDLE_PTR pxObjectHandle,
                                        mbedtls_pk_context * pxMbedPkContext );

/* Import the specified private key into storage. */
static CK_RV xProvisionPrivateKey( CK_SESSION_HANDLE xSession,
                                   uint8_t * pucPrivateKey,
                                   size_t xPrivateKeyLength,
                                   uint8_t * pucLabel,
                                   CK_OBJECT_HANDLE_PTR pxObjectHandle );

/* Import the specified public key into storage. */
static CK_RV xProvisionPublicKey( CK_SESSION_HANDLE xSession,
                                  uint8_t * pucKey,
                                  size_t xKeyLength,
                                  CK_KEY_TYPE xPublicKeyType,
                                  uint8_t * pucPublicKeyLabel,
                                  CK_OBJECT_HANDLE_PTR pxPublicKeyHandle );

static CK_RV xProvisionGenerateKeyPairEC( CK_SESSION_HANDLE xSession,
                                          uint8_t * pucPrivateKeyLabel,
                                          uint8_t * pucPublicKeyLabel,
                                          CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                                          CK_OBJECT_HANDLE_PTR pxPublicKeyHandle );

/*-----------------------------------------------------------*/

/* Import the specified X.509 client certificate into storage. */
static CK_RV xProvisionCertificate( CK_SESSION_HANDLE xSession,
                                    uint8_t * pucCertificate,
                                    size_t xCertificateLength,
                                    uint8_t * pucLabel,
                                    CK_OBJECT_HANDLE_PTR pxObjectHandle );

/*-----------------------------------------------------------*/

/* Delete the specified crypto object from storage. */
static CK_RV xDestroyProvidedObjects( CK_SESSION_HANDLE xSession,
                                      CK_BYTE_PTR * ppxPkcsLabels,
                                      CK_OBJECT_CLASS * xClass,
                                      CK_ULONG ulCount );
/*-----------------------------------------------------------*/

/* ============================   UNITY FIXTURES ============================ */
/* Called before each test method. */
void setUp()
{
    CK_RV xResult;

    xResult = C_GetFunctionList( &pxGlobalFunctionList );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get PKCS #11 function list." );

    xResult = xInitializePKCS11();

    if( xResult != CKR_CRYPTOKI_ALREADY_INITIALIZED )
    {
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to initialize PKCS #11 module." );
    }

    xResult = xInitializePkcs11Session( &xGlobalSession );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to open PKCS #11 session." );
}

/* Called after each test method. */
void tearDown()
{
    CK_RV xResult;

    xResult = pxGlobalFunctionList->C_CloseSession( xGlobalSession );

    if( xResult != CKR_CRYPTOKI_NOT_INITIALIZED )
    {
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to close session." );

        xResult = pxGlobalFunctionList->C_Finalize( NULL );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to finalize session." );
    }
}

/* ========================== Test Cases ============================ */

/* Delete well-known crypto objects from storage. */

static CK_RV prvDestroyTestCredentials( void )
{
    CK_RV xResult = CKR_OK;
    CK_RV xDestroyResult = CKR_OK;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_ULONG ulLabelCount = 0;

    CK_BYTE * pxPkcsLabels[] =
    {
        ( CK_BYTE * ) pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS,
        ( CK_BYTE * ) pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
        ( CK_BYTE * ) pkcs11testLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
        #if ( pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED == 1 )
            ( CK_BYTE * ) pkcs11testLABEL_CODE_VERIFICATION_KEY,
            ( CK_BYTE * ) pkcs11testLABEL_JITP_CERTIFICATE,
            ( CK_BYTE * ) pkcs11testLABEL_ROOT_CERTIFICATE
        #endif
    };
    CK_OBJECT_CLASS xClass[] =
    {
        CKO_CERTIFICATE,
        CKO_PRIVATE_KEY,
        CKO_PUBLIC_KEY,
        #if ( pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED == 1 )
            CKO_PUBLIC_KEY,
            CKO_CERTIFICATE,
            CKO_CERTIFICATE
        #endif
    };

    xDestroyResult = xDestroyProvidedObjects( xGlobalSession,
                                              pxPkcsLabels,
                                              xClass,
                                              sizeof( xClass ) / sizeof( CK_OBJECT_CLASS ) );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to destroy credentials." );

    for( ulLabelCount = 0;
         ulLabelCount < sizeof( xClass ) / sizeof( CK_OBJECT_CLASS );
         ulLabelCount++ )
    {
        xResult = xFindObjectWithLabelAndClass( xGlobalSession,
                                                ( char * ) pxPkcsLabels[ ulLabelCount ],
                                                xClass[ ulLabelCount ],
                                                &xObject );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Found an object after deleting it.\r\n" );
        TEST_ASSERT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xObject, "Object found after it was destroyed.\r\n" );
    }

    return xDestroyResult;
}

/* Assumes that device is already provisioned at time of calling. */
static void prvFindObjectTest( CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                               CK_OBJECT_HANDLE_PTR pxCertificateHandle,
                               CK_OBJECT_HANDLE_PTR pxPublicKeyHandle )
{
    CK_RV xResult;
    CK_OBJECT_HANDLE xTestObjectHandle = CK_INVALID_HANDLE;

    /* Happy Path - Find a previously created object. */
    xResult = xFindObjectWithLabelAndClass( xGlobalSession,
                                            pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                                            CKO_PRIVATE_KEY,
                                            pxPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find private key after closing and reopening a session." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxPrivateKeyHandle, "Invalid object handle found for  private key." );

    /* TODO: Add the code sign key and root ca. */
    xResult = xFindObjectWithLabelAndClass( xGlobalSession,
                                            pkcs11testLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
                                            CKO_PUBLIC_KEY,
                                            pxPublicKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find public key after closing and reopening a session." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxPublicKeyHandle, "Invalid object handle found for public key key." );


    xResult = xFindObjectWithLabelAndClass( xGlobalSession,
                                            pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                            CKO_CERTIFICATE,
                                            pxCertificateHandle );

    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find certificate after closing and reopening a session." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxCertificateHandle, "Invalid object handle found for certificate." );

    /* Try to find an object that has never been created. */
    xResult = xFindObjectWithLabelAndClass( xGlobalSession,
                                            ( char * ) "This label doesn't exist",
                                            CKO_PUBLIC_KEY,
                                            &xTestObjectHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Incorrect error code finding object that doesn't exist" );
    TEST_ASSERT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xTestObjectHandle, "Incorrect error code finding object that doesn't exist" );
}


/*-----------------------------------------------------------*/

void test_Get_Function_List( void )
{
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;

    TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, C_GetFunctionList( NULL ) );

    TEST_ASSERT_EQUAL( CKR_OK, C_GetFunctionList( &pxFunctionList ) );

    /* Ensure that pxFunctionList was changed by C_GetFunctionList. */
    TEST_ASSERT_NOT_EQUAL( NULL, pxFunctionList );
}

void test_Initialize_Finalize( void )
{
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_RV xResult;

    xResult = C_GetFunctionList( &pxFunctionList );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get function list." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( NULL, pxFunctionList, "Invalid function list pointer." );

    /* Set up will initialize, get it back to a known state. */
    xResult = pxFunctionList->C_Finalize( NULL );

    xResult = xInitializePKCS11();
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to initialize PKCS #11 module." );

    if( TEST_PROTECT() )
    {
        /* Call initialize a second time.  Since this call may be made many times,
         * it is important that PKCS #11 implementations be tolerant of multiple calls. */
        xResult = xInitializePKCS11();
        TEST_ASSERT_EQUAL_MESSAGE( CKR_CRYPTOKI_ALREADY_INITIALIZED, xResult, "Second PKCS #11 module initialization. " );

        /* C_Finalize should fail if pReserved isn't NULL. */
        xResult = pxFunctionList->C_Finalize( ( CK_VOID_PTR ) 0x1234 );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_ARGUMENTS_BAD, xResult, "Negative Test: Finalize with invalid argument" );
    }

    xResult = pxFunctionList->C_Finalize( NULL );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Finalize failed" );
}

void test_GetSlotList( void )
{
    CK_RV xResult;
    CK_SLOT_ID * pxSlotId = NULL;
    CK_ULONG xSlotCount = 0;
    CK_ULONG xExtraSlotCount = 0;

    if( TEST_PROTECT() )
    {
        /* The Happy Path. */

        /* When a NULL slot pointer is passed in,
         *  the number of slots should be updated. */
        xResult = pxGlobalFunctionList->C_GetSlotList( CK_TRUE, NULL, &xSlotCount );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get slot count" );
        TEST_ASSERT_GREATER_THAN_MESSAGE( 0, xSlotCount, "Slot count incorrectly updated" );

        /* Allocate memory to receive the list of slots, plus one extra. */
        pxSlotId = PKCS11_MALLOC( sizeof( CK_SLOT_ID ) * ( xSlotCount + 1 ) );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( NULL, pxSlotId, "Failed malloc memory for slot list" );

        /* Call C_GetSlotList again to receive all slots with tokens present. */
        xResult = pxGlobalFunctionList->C_GetSlotList( CK_TRUE, pxSlotId, &xSlotCount );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get slot count" );

        /* Note: Being able to use the slot to open a session will be  tested
         * in the C_OpenSession tests. */

        /* Off the happy path. */
        xExtraSlotCount = xSlotCount + 1;

        /* Make sure that number of slots returned is updated when extra buffer room exists. */
        xResult = pxGlobalFunctionList->C_GetSlotList( CK_TRUE, pxSlotId, &xExtraSlotCount );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get slot list" );
        TEST_ASSERT_EQUAL_MESSAGE( xSlotCount, xExtraSlotCount, "Failed to update the number of slots" );

        /* Claim that the buffer to receive slots is too small. */
        xSlotCount = 0;
        xResult = pxGlobalFunctionList->C_GetSlotList( CK_TRUE, pxSlotId, &xSlotCount );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_BUFFER_TOO_SMALL, xResult, "Negative Test: Improper handling of too-small slot buffer" );
    }

    if( pxSlotId != NULL )
    {
        PKCS11_FREE( pxSlotId );
    }

    xResult = pxGlobalFunctionList->C_Finalize( NULL );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Finalize failed" );
}

void test_OpenSession_CloseSession( void )
{
    CK_SLOT_ID_PTR pxSlotId = NULL;
    CK_SLOT_ID xSlotId = 0;
    CK_ULONG xSlotCount = 0;
    CK_SESSION_HANDLE xSession = 0;
    CK_BBOOL xSessionOpen = CK_FALSE;
    CK_RV xResult = CKR_OK;

    if( TEST_PROTECT() )
    {
        xResult = xGetSlotList( &pxSlotId,
                                &xSlotCount );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get slot list" );

        xSlotId = pxSlotId[ pkcs11testSLOT_NUMBER ];
        PKCS11_FREE( pxSlotId ); /* xGetSlotList allocates memory. */
        TEST_ASSERT_GREATER_THAN( 0, xSlotCount );

        xResult = pxGlobalFunctionList->C_OpenSession( xSlotId,
                                                       CKF_SERIAL_SESSION, /* This flag is mandatory for PKCS #11 legacy reasons. */
                                                       NULL,               /* Application defined pointer. */
                                                       NULL,               /* Callback function. */
                                                       &xSession );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to open session" );
        xSessionOpen = CK_TRUE;
    }

    if( xSessionOpen )
    {
        xResult = pxGlobalFunctionList->C_CloseSession( xSession );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to close session." );
    }

    pxGlobalFunctionList->C_Finalize( NULL );


    /* Negative tests */

    /* Try to open a session without having initialized the module. */
    xResult = pxGlobalFunctionList->C_OpenSession( xSlotId,
                                                   CKF_SERIAL_SESSION, /* This flag is mandatory for PKCS #11 legacy reasons. */
                                                   NULL,               /* Application defined pointer. */
                                                   NULL,               /* Callback function. */
                                                   &xSession );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_CRYPTOKI_NOT_INITIALIZED, xResult, "Negative Test: Opened a session before initializing module." );
}

static CK_BYTE x896BitInput[] = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";

static CK_BYTE xSha256HashOf896BitInput[] =
{
    0xcf, 0x5b, 0x16, 0xa7, 0x78, 0xaf, 0x83, 0x80, 0x03, 0x6c, 0xe5, 0x9e, 0x7b, 0x04, 0x92, 0x37,
    0x0b, 0x24, 0x9b, 0x11, 0xe8, 0xf0, 0x7a, 0x51, 0xaf, 0xac, 0x45, 0x03, 0x7a, 0xfe, 0xe9, 0xd1
};

void test_Digest( void )
{
    CK_RV xResult = 0;

    CK_MECHANISM xDigestMechanism;

    CK_BYTE xDigestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG xDigestLength = 0;


    /* Hash with SHA256 */
    xDigestMechanism.mechanism = CKM_SHA256;

    xResult = pxGlobalFunctionList->C_DigestInit( xGlobalSession, &xDigestMechanism );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    /* Subtract one because this hash was performed on the characters without the null terminator. */
    xResult = pxGlobalFunctionList->C_DigestUpdate( xGlobalSession, x896BitInput, sizeof( x896BitInput ) - 1 );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    /* Call C_DigestFinal on a NULL buffer to get the buffer length required. */
    xResult = pxGlobalFunctionList->C_DigestFinal( xGlobalSession, NULL, &xDigestLength );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
    TEST_ASSERT_EQUAL( pkcs11SHA256_DIGEST_LENGTH, xDigestLength );

    xResult = pxGlobalFunctionList->C_DigestFinal( xGlobalSession, xDigestResult, &xDigestLength );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
    TEST_ASSERT_EQUAL_INT8_ARRAY( xSha256HashOf896BitInput, xDigestResult, pkcs11SHA256_DIGEST_LENGTH );
}

void test_Digest_ErrorConditions( void )
{
    CK_RV xResult = 0;
    CK_MECHANISM xDigestMechanism;
    CK_BYTE xDigestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG xDigestLength = 0;

    /* Make sure that no NULL pointers in functions to be called in this test. */
    TEST_ASSERT_NOT_EQUAL( NULL, pxGlobalFunctionList->C_DigestInit );
    TEST_ASSERT_NOT_EQUAL( NULL, pxGlobalFunctionList->C_DigestUpdate );
    TEST_ASSERT_NOT_EQUAL( NULL, pxGlobalFunctionList->C_DigestFinal );

    /* Invalid hash mechanism. */
    xDigestMechanism.mechanism = 0x253; /*253 doesn't correspond to anything. */ /*CKM_MD5; */

    xResult = pxGlobalFunctionList->C_DigestInit( xGlobalSession, &xDigestMechanism );
    TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

    /* Null Session. */
    xDigestMechanism.mechanism = CKM_SHA256;
    xResult = pxGlobalFunctionList->C_DigestInit( ( CK_SESSION_HANDLE ) NULL, &xDigestMechanism );
    TEST_ASSERT_EQUAL( CKR_SESSION_HANDLE_INVALID, xResult );

    /* Make sure that digest update fails if DigestInit did not succeed. */
    xResult = pxGlobalFunctionList->C_DigestUpdate( xGlobalSession, x896BitInput, sizeof( x896BitInput ) - 1 );
    TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );

    /* Initialize the session properly. */
    xResult = pxGlobalFunctionList->C_DigestInit( xGlobalSession, &xDigestMechanism );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    /* Try to update digest with a NULL session handle. */
    xResult = pxGlobalFunctionList->C_DigestUpdate( ( CK_SESSION_HANDLE ) NULL, x896BitInput, sizeof( x896BitInput ) - 1 );
    TEST_ASSERT_EQUAL( CKR_SESSION_HANDLE_INVALID, xResult );

    /* DigestUpdate correctly.  Note that digest is not terminated because we didn't tell the session handle last time. */
    xResult = pxGlobalFunctionList->C_DigestUpdate( xGlobalSession, x896BitInput, sizeof( x896BitInput ) - 1 );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    /* Call C_DigestFinal on a buffer that is too small. */
    xDigestLength = pkcs11SHA256_DIGEST_LENGTH - 1;
    xResult = pxGlobalFunctionList->C_DigestFinal( xGlobalSession, xDigestResult, &xDigestLength );
    TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );

    /* Call C_DigestFinal on a NULL session handle. */
    xDigestLength = pkcs11SHA256_DIGEST_LENGTH;
    xResult = pxGlobalFunctionList->C_DigestFinal( ( CK_SESSION_HANDLE ) NULL, xDigestResult, &xDigestLength );
    TEST_ASSERT_EQUAL( CKR_SESSION_HANDLE_INVALID, xResult );

    /* Call C_DigestFinal on a proper buffer size. Note that Digest is not terminated if error is "buffer too small" or if session handle wasn't present. */
    xDigestLength = pkcs11SHA256_DIGEST_LENGTH;
    xResult = pxGlobalFunctionList->C_DigestFinal( xGlobalSession, xDigestResult, &xDigestLength );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
    TEST_ASSERT_EQUAL_INT8_ARRAY( xSha256HashOf896BitInput, xDigestResult, pkcs11SHA256_DIGEST_LENGTH );

    /* Call C_DigestUpdate after the digest operation has been completed. */
    xResult = pxGlobalFunctionList->C_DigestUpdate( xGlobalSession, x896BitInput, sizeof( x896BitInput ) - 1 );
    TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );
}

void test_GenerateRandom( void )
{
    CK_RV xResult = 0;
    uint32_t xSameSession = 0;
    uint32_t xDifferentSessions = 0;
    int i;

    CK_BYTE xBuf1[ pkcstestRAND_BUFFER_SIZE ];
    CK_BYTE xBuf2[ pkcstestRAND_BUFFER_SIZE ];
    CK_BYTE xBuf3[ pkcstestRAND_BUFFER_SIZE ];

    /* Generate random bytes twice. */
    if( CKR_OK == xResult )
    {
        xResult = pxGlobalFunctionList->C_GenerateRandom( xGlobalSession, xBuf1, pkcstestRAND_BUFFER_SIZE );
    }

    if( CKR_OK == xResult )
    {
        xResult = pxGlobalFunctionList->C_GenerateRandom( xGlobalSession, xBuf2, pkcstestRAND_BUFFER_SIZE );
    }

    if( CKR_OK == xResult )
    {
        /* Close the session and PKCS #11 module */
        if( NULL != pxGlobalFunctionList )
        {
            ( void ) pxGlobalFunctionList->C_CloseSession( xGlobalSession );
        }
    }

    /* Re-open PKCS #11 session. */
    xResult = xInitializePkcs11Session( &xGlobalSession );

    if( CKR_OK == xResult )
    {
        xResult = pxGlobalFunctionList->C_GenerateRandom( xGlobalSession, xBuf3, pkcstestRAND_BUFFER_SIZE );
    }

    /* Check that the result is good. */
    TEST_ASSERT_EQUAL_INT32( CKR_OK, xResult );

    /* Check that the random bytes generated within session
     * and between initializations of PKCS module are not the same. */
    for( i = 0; i < pkcstestRAND_BUFFER_SIZE; i++ )
    {
        if( xBuf1[ i ] == xBuf2[ i ] )
        {
            xSameSession++;
        }

        if( xBuf1[ i ] == xBuf3[ i ] )
        {
            xDifferentSessions++;
        }
    }

    if( ( xSameSession > 1 ) || ( xDifferentSessions > 1 ) )
    {
        LogDebug( ( "First Random Bytes: %02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X",
                    xBuf1[ 0 ], xBuf1[ 1 ], xBuf1[ 2 ], xBuf1[ 3 ], xBuf1[ 4 ],
                    xBuf1[ 5 ], xBuf1[ 6 ], xBuf1[ 7 ], xBuf1[ 8 ], xBuf1[ 9 ] ) );

        LogDebug( ( "Second Set of Random Bytes: %02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X",
                    xBuf2[ 0 ], xBuf2[ 1 ], xBuf2[ 2 ], xBuf2[ 3 ], xBuf2[ 4 ],
                    xBuf2[ 5 ], xBuf2[ 6 ], xBuf2[ 7 ], xBuf2[ 8 ], xBuf2[ 9 ] ) );

        LogDebug( ( "Third Set of Random Bytes:  %02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X:%02X",
                    xBuf3[ 0 ], xBuf3[ 1 ], xBuf3[ 2 ], xBuf3[ 3 ], xBuf3[ 4 ],
                    xBuf3[ 5 ], xBuf3[ 6 ], xBuf3[ 7 ], xBuf3[ 8 ], xBuf3[ 9 ] ) );
    }

    TEST_ASSERT_LESS_THAN( 2, xSameSession );
    TEST_ASSERT_LESS_THAN( 2, xDifferentSessions );
}

/* Valid RSA private key. */
static const char cValidRSAPrivateKey[] =
    "-----BEGIN RSA PRIVATE KEY-----\n"
    "MIIEpAIBAAKCAQEAsIqRecRxLz3PZXzZOHF7jMlB25tfv2LDGR7nGTJiey5zxd7o\n"
    "swihe7+26yx8medpNvX1ym9jphty+9IR053k1WGnQQ4aaDeJonqn7V50Vesw6zFx\n"
    "/x8LMdXFoBAkRXIL8WS5YKafC87KPnye8A0piVWUFy7+IEEaK3hQEJTzB6LC/N10\n"
    "0XL5ykLCa4xJBOqlIvbDvJ+bKty1EBA3sStlTNuXi3nBWZbXwCB2A+ddjijFf5+g\n"
    "Ujinr7h6e2uQeipWyiIw9NKWbvq8AG1Mj4XBoFL9wP2YTf2SQAgAzx0ySPNrIYOz\n"
    "BNl1YZ4lIW5sJLATES9+Z8nHi7yRDLw6x/kcVQIDAQABAoIBADd+h3ZIeu/HtT8I\n"
    "vNuSSK0bwpj+wV1O9VcbMLfp760bEAd+J5XHu8NDo4NPi6dxZ9CABpBo7WEUtdNU\n"
    "2Ie11W4B8WpwvXpPIvOxLMJf85/ie5EjDNuObZ1vvlyvVkeCLyDlcaRhHBPBIC/+\n"
    "SpPY/1qNTSzwd6+55zkM69YajD60tFv8WuCsgkAteCoDjcqwDcowyAy4pILhOYaW\n"
    "1x+0ZPMUqwtld+06ct/yqBPB8C9IH7ZIeJr5e58R9SxytbuTwTN4jceOoeD5MBbG\n"
    "A+A0WxGdQ8N+kwWkz77qDbZfP4G8wNxeUXobnfqfDGqb0O5zeEaU7EI+mlEQH58Z\n"
    "B1edj6ECgYEA3rldciCQc4t2qYKiZSffnl7Pg7L+ojzH/Eam4Dlk27+DqOo70MnX\n"
    "LVWUWkLOMQ27dRSBQsUDUaqVRZLkcFKc6C8k2cIpPBMpA9WdZVd9kFawZ8lJ7jko\n"
    "qTbJxnDxvhdHrZRvLRjEenbdNXdAGy2EuqvThUJgPEybLAWg6sE3LB0CgYEAyurT\n"
    "14h4BGEGBpl2KevoPQ4PPS+IoDXMS29mtfcascVkYcxxW1v8wOQVyD4VrsRMErck\n"
    "ZMpu2evd+aQSPSrAod/sQ20C+wCCA7ipBlhAUeuS/FpqFIZWkHzZnVccp8O3nOFO\n"
    "KNeAmw4udq8PyjVVouey/6F386itJdxWt/d8i5kCgYA3Aru045wqHck6RvzLVVTj\n"
    "LfG9Sqmf8rlGc0DmYuapbB0dzHTnteLC3L9ep997uDOT0HO4xSZztllWLNjlcVI1\n"
    "+ub0LgO3Rdg8jTdp/3kQ/IhnqgzrnQyQ9upRbDYZSHC4y8/F6LcmtFMg0Ipx7AU7\n"
    "ghMld+aDHjy5W86KDR0OdQKBgQCAZoPSONqo+rQTbPwmns6AA+uErhVoO2KgwUdf\n"
    "EZPktaFFeVapltWjQTC/WvnhcvkoRpdS5/2pC+WUWEvqRKlMRSN9rvdZ2QJsVGcw\n"
    "Spu4urZx1MyXXEJef4I8W6kYR3JiZPdORL9uXlTsaO425/Tednr/4y7CEhQuhvSg\n"
    "yIwY0QKBgQC2NtKDOwcgFykKRYqtHuo6VpSeLmgm1DjlcAuaGJsblX7C07ZH8Tjm\n"
    "IHQb01oThNEa4tC0vO3518PkQwvyi/TWGHm9SLYdXvpVnBwkk5yRioKPgPmrs4Xi\n"
    "ERIYrvveGGtQ3vSknLWUJ/0BgmuYj5U6aJBZPv8COM2eKIbTQbtQaQ==\n"
    "-----END RSA PRIVATE KEY-----\n";

/* Valid RSA certificate. */
static const char cValidRSACertificate[] =
    "-----BEGIN CERTIFICATE-----\n"
    "MIIDsTCCApmgAwIBAgIJALg4YJlPspxyMA0GCSqGSIb3DQEBCwUAMG8xCzAJBgNV\n"
    "BAYTAlVTMQswCQYDVQQIDAJXQTEQMA4GA1UEBwwHU2VhdHRsZTENMAsGA1UECgwE\n"
    "QW16bjEMMAoGA1UECwwDSW9UMQ0wCwYDVQQDDARUZXN0MRUwEwYJKoZIhvcNAQkB\n"
    "FgZub2JvZHkwHhcNMTgwNjExMTk0NjM2WhcNMjEwMzMxMTk0NjM2WjBvMQswCQYD\n"
    "VQQGEwJVUzELMAkGA1UECAwCV0ExEDAOBgNVBAcMB1NlYXR0bGUxDTALBgNVBAoM\n"
    "BEFtem4xDDAKBgNVBAsMA0lvVDENMAsGA1UEAwwEVGVzdDEVMBMGCSqGSIb3DQEJ\n"
    "ARYGbm9ib2R5MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAsIqRecRx\n"
    "Lz3PZXzZOHF7jMlB25tfv2LDGR7nGTJiey5zxd7oswihe7+26yx8medpNvX1ym9j\n"
    "phty+9IR053k1WGnQQ4aaDeJonqn7V50Vesw6zFx/x8LMdXFoBAkRXIL8WS5YKaf\n"
    "C87KPnye8A0piVWUFy7+IEEaK3hQEJTzB6LC/N100XL5ykLCa4xJBOqlIvbDvJ+b\n"
    "Kty1EBA3sStlTNuXi3nBWZbXwCB2A+ddjijFf5+gUjinr7h6e2uQeipWyiIw9NKW\n"
    "bvq8AG1Mj4XBoFL9wP2YTf2SQAgAzx0ySPNrIYOzBNl1YZ4lIW5sJLATES9+Z8nH\n"
    "i7yRDLw6x/kcVQIDAQABo1AwTjAdBgNVHQ4EFgQUHc4PjEL0CaxZ+1D/4VdeDjxt\n"
    "JO8wHwYDVR0jBBgwFoAUHc4PjEL0CaxZ+1D/4VdeDjxtJO8wDAYDVR0TBAUwAwEB\n"
    "/zANBgkqhkiG9w0BAQsFAAOCAQEAi1/okTpQuPcaQEBgepccZ/Lt/gEQNdGcbsYQ\n"
    "3aEABNVYL8dYOW9r/8l074zD+vi9iSli/yYmwRFD0baN1FRWUqkVEIQ+3yfivOW9\n"
    "R282NuQvEULgERC2KN7vm0vO+DF7ay58qm4PaAGHdQco1LaHKkljMPLHF841facG\n"
    "M9KVtzFveOQKkWvb4VgOyfn7aCnEogGlWt1S0d12pBRwYjJgKrVQaGs6IiGFVtm8\n"
    "JRLZrLL3sfgsN7L1xu//JUoTOkgxdKuYRmPuUdV2hw/VYDzcnKj7/DMXNDvgl3s7\n"
    "5GC4F+8LFLzRrZJWs18FMLaCE+zJChw/oeSt+RS0JZDFn+uX9Q==\n"
    "-----END CERTIFICATE-----\n";

void prvProvisionRsaTestCredentials( CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                                     CK_OBJECT_HANDLE_PTR pxCertificateHandle )
{
    CK_RV xResult;

    /* Create a private key. */
    xResult = xProvisionPrivateKey( xGlobalSession,
                                    ( uint8_t * ) cValidRSAPrivateKey,
                                    sizeof( cValidRSAPrivateKey ),
                                    ( uint8_t * ) pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                                    pxPrivateKeyHandle );

    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create RSA private key." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxPrivateKeyHandle, "Invalid object handle returned for RSA private key." );

    /* Create a certificate. */
    xResult = xProvisionCertificate( xGlobalSession,
                                     ( uint8_t * ) cValidRSACertificate,
                                     sizeof( cValidRSACertificate ),
                                     ( uint8_t * ) pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                     pxCertificateHandle );

    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create RSA certificate." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxCertificateHandle, "Invalid object handle returned for RSA certificate." );
}

void test_CreateObject_RSA( void )
{
    CK_RV xResult;
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xCertificateHandle = CK_INVALID_HANDLE;

    xResult = prvDestroyTestCredentials();
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to destroy credentials in test setup." );

    prvProvisionRsaTestCredentials( &xPrivateKeyHandle, &xCertificateHandle );
}

void test_FindObject_RSA( void )
{
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xCertificateHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPublicKeyHandle = CK_INVALID_HANDLE;

    prvFindObjectTest( &xPrivateKeyHandle, &xCertificateHandle, &xPublicKeyHandle );
}

void test_GetAttributeValue_RSA( void )
{
    CK_RV xResult;
    CK_ATTRIBUTE xTemplate;
    CK_OBJECT_HANDLE xCertificateHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;


    CK_BYTE xCertificateValue[ CERTIFICATE_VALUE_LENGTH ];
    CK_BYTE xKeyComponent[ ( pkcs11RSA_2048_MODULUS_BITS / 8 ) + 1 ] = { 0 };

    xResult = xFindObjectWithLabelAndClass( xGlobalSession, pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, CKO_PRIVATE_KEY, &xPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find RSA private key." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xPrivateKeyHandle, "Invalid object handle found for RSA private key." );

    xResult = xFindObjectWithLabelAndClass( xGlobalSession, pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS, CKO_CERTIFICATE, &xCertificateHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find RSA certificate." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xCertificateHandle, "Invalid object handle found for RSA certificate." );

    /* TODO: Add RSA key component GetAttributeValue checks. */
    /* Get the certificate value. */
    xTemplate.type = CKA_VALUE;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xCertificateHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CERTIFICATE_VALUE_LENGTH, xTemplate.ulValueLen, "GetAttributeValue returned incorrect length of RSA certificate value" );

    xTemplate.pValue = xCertificateValue;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xCertificateHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to get RSA certificate value" );
    TEST_ASSERT_EQUAL_MESSAGE( CERTIFICATE_VALUE_LENGTH, xTemplate.ulValueLen, "GetAttributeValue returned incorrect length of RSA certificate value" );
    /* TODO: Check byte array */

    /* Check that the private key cannot be retrieved. */
    xTemplate.type = CKA_PRIVATE_EXPONENT;
    xTemplate.pValue = xKeyComponent;
    xTemplate.ulValueLen = sizeof( xKeyComponent );
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_ATTRIBUTE_SENSITIVE, xResult, "Incorrect error code retrieved when trying to obtain private key." );
    TEST_ASSERT_EACH_EQUAL_INT8_MESSAGE( 0, xKeyComponent, sizeof( xKeyComponent ), "Private key bytes returned when they should not be." );
}


void test_Sign_RSA( void )
{
    CK_RV xResult;
    CK_OBJECT_HANDLE xPrivateKeyHandle;
    CK_OBJECT_HANDLE xCertificateHandle;
    CK_MECHANISM xMechanism;
    CK_BYTE xHashedMessage[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_BYTE xSignature[ pkcs11RSA_2048_SIGNATURE_LENGTH ] = { 0 };
    CK_ULONG xSignatureLength;
    CK_BYTE xHashPlusOid[ pkcs11RSA_SIGNATURE_INPUT_LENGTH ];

    prvProvisionRsaTestCredentials( &xPrivateKeyHandle, &xCertificateHandle );

    xResult = vAppendSHA256AlgorithmIdentifierSequence( xHashedMessage, xHashPlusOid );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to append hash algorithm to RSA signature material." );

    /* The RSA X.509 mechanism assumes a pre-hashed input. */
    xMechanism.mechanism = CKM_RSA_PKCS;
    xMechanism.pParameter = NULL;
    xMechanism.ulParameterLen = 0;
    xResult = pxGlobalFunctionList->C_SignInit( xGlobalSession, &xMechanism, xPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to SignInit RSA." );

    xSignatureLength = sizeof( xSignature );
    xResult = pxGlobalFunctionList->C_Sign( xGlobalSession, xHashPlusOid, sizeof( xHashPlusOid ), xSignature, &xSignatureLength );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to RSA Sign." );
    TEST_ASSERT_EQUAL_MESSAGE( pkcs11RSA_2048_SIGNATURE_LENGTH, xSignatureLength, "RSA Sign returned an unexpected signature length." );

    xResult = pxGlobalFunctionList->C_SignInit( xGlobalSession, &xMechanism, xPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to SignInit RSA." );

    xResult = pxGlobalFunctionList->C_Sign( xGlobalSession, xHashPlusOid, sizeof( xHashPlusOid ), NULL, &xSignatureLength );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to RSA Sign." );
    TEST_ASSERT_EQUAL_MESSAGE( pkcs11RSA_2048_SIGNATURE_LENGTH, xSignatureLength, "RSA Sign should return needed signature buffer length when pucSignature is NULL." );

    /* Verify the signature with mbedTLS */
    mbedtls_pk_context xMbedPkContext;
    int lMbedTLSResult;

    mbedtls_pk_init( &xMbedPkContext );

    if( TEST_PROTECT() )
    {
        lMbedTLSResult = mbedtls_pk_parse_key( ( mbedtls_pk_context * ) &xMbedPkContext,
                                               ( const unsigned char * ) cValidRSAPrivateKey,
                                               sizeof( cValidRSAPrivateKey ),
                                               NULL,
                                               0 );

        lMbedTLSResult = mbedtls_rsa_pkcs1_verify( xMbedPkContext.pk_ctx, NULL, NULL, MBEDTLS_RSA_PUBLIC, MBEDTLS_MD_SHA256, 32, xHashedMessage, xSignature );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedTLSResult, "mbedTLS failed to parse valid RSA key (verification)" );
    }

    mbedtls_pk_free( &xMbedPkContext );
}


void test_DestroyObject_RSA( void )
{
    CK_RV xResult = CKR_OK;

    xResult = prvDestroyTestCredentials();
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to destroy RSA credentials." );
}


/* Valid ECDSA private key. */
static const char cValidECDSAPrivateKey[] =
    "-----BEGIN EC PRIVATE KEY-----\n"
    "MHcCAQEEIACZbHljxOFuBeEKRcMijfbVcDzBxa8M4T5jElsElFQ5oAoGCCqGSM49\n"
    "AwEHoUQDQgAEzghp+QstUhOmzKBGEL7uBjsaBbyaNTMLXKLSW78+bdoP9bKTOrqi\n"
    "Kk9GzFk9ChthHFsx+T7UFithbYWtRf0Zww==\n"
    "-----END EC PRIVATE KEY-----";

/* Valid ECDSA public key. */
static const char cValidECDSAPublicKey[] =
    "-----BEGIN PUBLIC KEY-----\n"
    "MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEzghp+QstUhOmzKBGEL7uBjsaBbya\n"
    "NTMLXKLSW78+bdoP9bKTOrqiKk9GzFk9ChthHFsx+T7UFithbYWtRf0Zww==\n"
    "-----END PUBLIC KEY-----";

/* Valid ECDSA certificate. */
static const char cValidECDSACertificate[] =
    "-----BEGIN CERTIFICATE-----\n"
    "MIICbjCCAhQCCQDqQDa2NeYOhTAKBggqhkjOPQQDAjCBvjELMAkGA1UEBhMCVVMx\n"
    "EzARBgNVBAgMCldhc2hpbmd0b24xEDAOBgNVBAcMB1NlYXR0bGUxGDAWBgNVBAoM\n"
    "D0FtYXpvbiBGcmVlUlRPUzEhMB8GA1UECwwYUEtDUyAjMTEgVGVzdCBDcmVkZW50\n"
    "aWFsMSgwJgYDVQQDDB9ET05UX1VTRV9USElTX0tFWV9JTl9BX1JFQUxfQVBQMSEw\n"
    "HwYJKoZIhvcNAQkBFhJub2JvZHlAbm93aGVyZS5jb20wHhcNMTkwNTI5MjE1NjAw\n"
    "WhcNMjkwNTI2MjE1NjAwWjCBvjELMAkGA1UEBhMCVVMxEzARBgNVBAgMCldhc2hp\n"
    "bmd0b24xEDAOBgNVBAcMB1NlYXR0bGUxGDAWBgNVBAoMD0FtYXpvbiBGcmVlUlRP\n"
    "UzEhMB8GA1UECwwYUEtDUyAjMTEgVGVzdCBDcmVkZW50aWFsMSgwJgYDVQQDDB9E\n"
    "T05UX1VTRV9USElTX0tFWV9JTl9BX1JFQUxfQVBQMSEwHwYJKoZIhvcNAQkBFhJu\n"
    "b2JvZHlAbm93aGVyZS5jb20wWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAATOCGn5\n"
    "Cy1SE6bMoEYQvu4GOxoFvJo1MwtcotJbvz5t2g/1spM6uqIqT0bMWT0KG2EcWzH5\n"
    "PtQWK2Ftha1F/RnDMAoGCCqGSM49BAMCA0gAMEUCIQCs1n3p+fOZxjZT+fnm3MQf\n"
    "IhxppLKnUggV42SAMpSneQIgdufH9clHZgrd9HVpRlIumy3sIMNEu9fzC9XZsSu8\n"
    "yQ8=\n"
    "-----END CERTIFICATE-----";

void prvProvisionCredentialsWithKeyImport( CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                                           CK_OBJECT_HANDLE_PTR pxCertificateHandle,
                                           CK_OBJECT_HANDLE_PTR pxPublicKeyHandle )
{
    CK_RV xResult;


    xResult = prvDestroyTestCredentials();
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to destroy credentials in test setup." );

    xResult = xProvisionPublicKey( xGlobalSession,
                                   ( uint8_t * ) cValidECDSAPublicKey,
                                   sizeof( cValidECDSAPublicKey ),
                                   CKK_EC,
                                   ( uint8_t * ) pkcs11testLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
                                   pxPublicKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create EC public key." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( 0, *pxPublicKeyHandle, "Invalid object handle returned for EC public key." );

    xResult = xProvisionPrivateKey( xGlobalSession,
                                    ( uint8_t * ) cValidECDSAPrivateKey,
                                    sizeof( cValidECDSAPrivateKey ),
                                    ( uint8_t * ) pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                                    pxPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create EC private key." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( 0, *pxPrivateKeyHandle, "Invalid object handle returned for EC private key." );

    xResult = xProvisionCertificate( xGlobalSession,
                                     ( uint8_t * ) cValidECDSACertificate,
                                     sizeof( cValidECDSACertificate ),
                                     ( uint8_t * ) pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                     pxCertificateHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create EC certificate." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( 0, *pxCertificateHandle, "Invalid object handle returned for EC certificate." );
}

void prvProvisionCredentialsWithGenerateKeyPair( CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                                                 CK_OBJECT_HANDLE_PTR pxCertificateHandle,
                                                 CK_OBJECT_HANDLE_PTR pxPublicKeyHandle )
{
    CK_RV xResult;
    CK_ATTRIBUTE xTemplate;
    CK_KEY_TYPE xKeyType = 0;
    CK_BBOOL xProvisionKeyNeeded = CK_FALSE;

    /* Check if there is an EC private key in there already. */
    xResult = xFindObjectWithLabelAndClass( xGlobalSession, pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, CKO_PRIVATE_KEY, pxPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find private key." );
    xResult = xFindObjectWithLabelAndClass( xGlobalSession, pkcs11testLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, CKO_PUBLIC_KEY, pxPublicKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find public key." );

    if( *pxPrivateKeyHandle != CK_INVALID_HANDLE )
    {
        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = &xKeyType;
        xTemplate.ulValueLen = sizeof( CK_KEY_TYPE );
        xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, *pxPrivateKeyHandle, &xTemplate, 1 );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to find private key's type." );

        if( xKeyType != CKK_EC )
        {
            xProvisionKeyNeeded = CK_TRUE;
        }
    }

    if( *pxPrivateKeyHandle == CK_INVALID_HANDLE )
    {
        xProvisionKeyNeeded = CK_TRUE;
    }

    if( xProvisionKeyNeeded == CK_TRUE )
    {
        xResult = xProvisionGenerateKeyPairEC( xGlobalSession, ( uint8_t * ) pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS, ( uint8_t * ) pkcs11testLABEL_DEVICE_PUBLIC_KEY_FOR_TLS, pxPrivateKeyHandle, pxPublicKeyHandle );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to generate key pair." );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxPrivateKeyHandle, "Invalid object handle returned for EC private key." );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, *pxPublicKeyHandle, "Invalid object handle returned for EC public key." );
    }

    xResult = xFindObjectWithLabelAndClass( xGlobalSession, pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS, CKO_CERTIFICATE, pxCertificateHandle );

    /* NOTE: This certificate is for object storage and retrieval purposes only, and does not correspond to the key pair generated. */
    if( *pxCertificateHandle == CK_INVALID_HANDLE )
    {
        xResult = xProvisionCertificate( xGlobalSession,
                                         ( uint8_t * ) cValidECDSACertificate,
                                         sizeof( cValidECDSACertificate ),
                                         ( uint8_t * ) pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                         pxCertificateHandle );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create EC certificate." );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( 0, *pxPrivateKeyHandle, "Invalid object handle returned for EC certificate." );
    }
}


void prvProvisionEcTestCredentials( CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                                    CK_OBJECT_HANDLE_PTR pxCertificateHandle,
                                    CK_OBJECT_HANDLE_PTR pxPublicKeyHandle )
{
    #if ( pkcs11testIMPORT_PRIVATE_KEY_SUPPORT != 0 )
        prvProvisionCredentialsWithKeyImport( pxPrivateKeyHandle, pxCertificateHandle, pxPublicKeyHandle );
    #else
        prvProvisionCredentialsWithGenerateKeyPair( pxPrivateKeyHandle, pxCertificateHandle, pxPublicKeyHandle );
    #endif
}

void test_DestoryObject_EC( void )
{
    CK_RV xResult;

    xResult = prvDestroyTestCredentials();
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK,
                               xResult,
                               "Failed to destroy credentials in test setup." );
}

void test_CreateObject_EC( void )
{
    CK_OBJECT_HANDLE xPrivateKeyHandle;
    CK_OBJECT_HANDLE xCertificateHandle;
    CK_OBJECT_HANDLE xPublicKeyHandle;

    #if ( pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED == 1 )
        CK_RV xResult;
        CK_OBJECT_HANDLE xRootCertificateHandle;
        CK_OBJECT_HANDLE xCodeSignPublicKeyHandle;
        CK_OBJECT_HANDLE xJITPCertificateHandle;
    #endif /* if ( pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED == 1 ) */

    /* Ignore result as this might fail if the credentials did not exist. */
    prvDestroyTestCredentials();

    prvProvisionCredentialsWithKeyImport( &xPrivateKeyHandle,
                                          &xCertificateHandle,
                                          &xPublicKeyHandle );

    #if ( pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED == 1 )
        xResult = xProvisionCertificate( xGlobalSession,
                                         ( uint8_t * ) tlsATS1_ROOT_CERTIFICATE_PEM,
                                         tlsATS1_ROOT_CERTIFICATE_LENGTH,
                                         pkcs11configLABEL_ROOT_CERTIFICATE,
                                         &xRootCertificateHandle );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create root EC certificate." );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xRootCertificateHandle, "Invalid object handle returned for EC root certificate." );

        xResult = xProvisionCertificate( xGlobalSession,
                                         ( uint8_t * ) tlsATS1_ROOT_CERTIFICATE_PEM,
                                         tlsATS1_ROOT_CERTIFICATE_LENGTH,
                                         pkcs11configLABEL_JITP_CERTIFICATE,
                                         &xJITPCertificateHandle );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create JITP EC certificate." );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xJITPCertificateHandle, "Invalid object handle returned for EC JITP certificate." );

        xResult = xProvisionPublicKey( xGlobalSession,
                                       ( uint8_t * ) cValidECDSAPublicKey,
                                       sizeof( cValidECDSAPrivateKey ),
                                       CKK_EC,
                                       pkcs11configLABEL_CODE_VERIFICATION_KEY,
                                       &xCodeSignPublicKeyHandle );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create EC code sign public key." );
        TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xCodeSignPublicKeyHandle, "Invalid object handle returned for EC code sign public key." );
    #endif /* if ( pkcs11configJITP_CODEVERIFY_ROOT_CERT_SUPPORTED == 1 ) */
}

void test_Sign_EC( void )
{
    CK_RV xResult = CKR_OK;
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPublicKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xCertificateHandle = CK_INVALID_HANDLE;

    /* Note that ECDSA operations on a signature of all 0's is not permitted. */
    CK_BYTE xHashedMessage[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xab };
    CK_MECHANISM xMechanism;
    CK_BYTE xSignature[ pkcs11RSA_2048_SIGNATURE_LENGTH ] = { 0 };
    CK_ULONG xSignatureLength;
    int lMbedTLSResult;

    /* Find objects that were previously created. This test case should be run if
     * there are objects that exists under known labels. This test case is not
     * responsible for creating the objects used for signing. */
    prvFindObjectTest( &xPrivateKeyHandle, &xCertificateHandle, &xPublicKeyHandle );

    xMechanism.mechanism = CKM_ECDSA;
    xMechanism.pParameter = NULL;
    xMechanism.ulParameterLen = 0;
    xResult = pxGlobalFunctionList->C_SignInit( xGlobalSession, &xMechanism, xPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to SignInit ECDSA." );

    xSignatureLength = sizeof( xSignature );
    xResult = pxGlobalFunctionList->C_Sign( xGlobalSession, xHashedMessage, pkcs11SHA256_DIGEST_LENGTH, xSignature, &xSignatureLength );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to ECDSA Sign." );
    TEST_ASSERT_EQUAL_MESSAGE( pkcs11ECDSA_P256_SIGNATURE_LENGTH, xSignatureLength, "ECDSA Sign returned an unexpected ECDSA Signature length." );

    xResult = pxGlobalFunctionList->C_SignInit( xGlobalSession, &xMechanism, xPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to SignInit ECDSA." );

    xResult = pxGlobalFunctionList->C_Sign( xGlobalSession, xHashedMessage, pkcs11SHA256_DIGEST_LENGTH, NULL, &xSignatureLength );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to ECDSA Sign." );
    TEST_ASSERT_EQUAL_MESSAGE( pkcs11ECDSA_P256_SIGNATURE_LENGTH, xSignatureLength, "ECDSA Sign should return needed signature buffer length when pucSignature is NULL." );

    /* Now extract the EC public key point so we can reconstruct it in mbed TLS. */
    mbedtls_pk_context xEcdsaContext;
    mbedtls_pk_context * pxEcdsaContext = &xEcdsaContext;
    CK_ATTRIBUTE xPubKeyQuery = { CKA_EC_POINT, NULL, 0 };
    CK_BYTE * pxPublicKey = NULL;
    mbedtls_pk_init( pxEcdsaContext );

    /* Reconstruct public key from EC Params. */
    mbedtls_ecp_keypair * pxKeyPair;
    pxKeyPair = PKCS11_MALLOC( sizeof( mbedtls_ecp_keypair ) );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( NULL, pxKeyPair, "Failed to allocate memory for the mbed TLS context." );

    /* Initialize the info. */
    pxEcdsaContext->pk_info = &mbedtls_eckey_info;
    mbedtls_ecp_keypair_init( pxKeyPair );
    mbedtls_ecp_group_init( &pxKeyPair->grp );

    /* Might want to make the ECP group configurable in the future. */
    lMbedTLSResult = mbedtls_ecp_group_load( &pxKeyPair->grp,
                                             MBEDTLS_ECP_DP_SECP256R1 );
    TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedTLSResult, "Failed to load EC group." );

    /* Initialize the context. */
    pxEcdsaContext->pk_ctx = pxKeyPair;

    /* Get EC point from PKCS #11 stack. */
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKeyHandle, &xPubKeyQuery, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to query for public key length" );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( 0, xPubKeyQuery.ulValueLen, "The size of the public key was an unexpected value." );

    pxPublicKey = PKCS11_MALLOC( xPubKeyQuery.ulValueLen );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( NULL, pxPublicKey, "Failed to allocate space for public key." );

    xPubKeyQuery.pValue = pxPublicKey;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKeyHandle, &xPubKeyQuery, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to query for public key length" );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( 0, xPubKeyQuery.ulValueLen, "The size of the public key was an unexpected value." );

    /* Strip the ANS.1 Encoding of type and length. Otherwise mbed TLS won't be
     * able to parse the binary EC point. */
    lMbedTLSResult = mbedtls_ecp_point_read_binary( &pxKeyPair->grp,
                                                    &pxKeyPair->Q,
                                                    ( uint8_t * ) ( xPubKeyQuery.pValue ) + 2,
                                                    xPubKeyQuery.ulValueLen - 2 );
    TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedTLSResult, "mbedTLS failed to read binary point." );

    if( TEST_PROTECT() )
    {
        mbedtls_ecp_keypair * pxEcdsaContext = ( mbedtls_ecp_keypair * ) xEcdsaContext.pk_ctx;
        /* An ECDSA signature is comprised of 2 components - R & S. */
        mbedtls_mpi xR;
        mbedtls_mpi xS;
        mbedtls_mpi_init( &xR );
        mbedtls_mpi_init( &xS );

        lMbedTLSResult = mbedtls_mpi_read_binary( &xR, &xSignature[ 0 ], 32 );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedTLSResult, "mbedTLS failed to read R binary in ECDSA signature." );

        lMbedTLSResult = mbedtls_mpi_read_binary( &xS, &xSignature[ 32 ], 32 );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedTLSResult, "mbedTLS failed to read S binary in ECDSA signature." );

        lMbedTLSResult = mbedtls_ecdsa_verify( &pxEcdsaContext->grp, xHashedMessage, sizeof( xHashedMessage ), &pxEcdsaContext->Q, &xR, &xS );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedTLSResult, "mbedTLS failed to verify signature." );

        mbedtls_mpi_free( &xR );
        mbedtls_mpi_free( &xS );
    }

    mbedtls_pk_free( &xEcdsaContext );
}

void test_Verify_EC( void )
{
    CK_RV xResult;
    CK_OBJECT_HANDLE xPrivateKeyHandle;
    CK_OBJECT_HANDLE xPublicKeyHandle;
    CK_OBJECT_HANDLE xCertificateHandle;
    CK_MECHANISM xMechanism;
    CK_BYTE xHashedMessage[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xbe };
    CK_BYTE xSignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH + 10 ] = { 0 };
    CK_BYTE xSignaturePKCS[ 64 ] = { 0 };
    size_t xSignatureLength = pkcs11ECDSA_P256_SIGNATURE_LENGTH;

    /* TODO: Consider switching this out for a C_GenerateRandom dependent function for ports not implementing mbedTLS. */

    /* Find objects that were previously created. This test case should be run if
     * there are objects that exists under known labels. This test case is not
     * responsible for creating the objects used for signing. */
    prvFindObjectTest( &xPrivateKeyHandle, &xCertificateHandle, &xPublicKeyHandle );

    /* Sign data w/ PKCS. */
    xMechanism.mechanism = CKM_ECDSA;
    xMechanism.pParameter = NULL;
    xMechanism.ulParameterLen = 0;
    xResult = pxGlobalFunctionList->C_SignInit( xGlobalSession, &xMechanism, xPrivateKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "SignInit failed." );
    xResult = pxGlobalFunctionList->C_Sign( xGlobalSession, xHashedMessage, sizeof( xHashedMessage ), xSignature, ( CK_ULONG * ) &xSignatureLength );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Sign failed." );

    xResult = pxGlobalFunctionList->C_VerifyInit( xGlobalSession, &xMechanism, xPublicKeyHandle );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "VerifyInit failed." );

    xResult = pxGlobalFunctionList->C_Verify( xGlobalSession, xHashedMessage, pkcs11SHA256_DIGEST_LENGTH, xSignature, sizeof( xSignaturePKCS ) );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Verify failed." );

    #if ( pkcs11testIMPORT_PRIVATE_KEY_SUPPORT == 1 )
        mbedtls_pk_context xPkContext;
        mbedtls_entropy_context xEntropyContext;
        mbedtls_ctr_drbg_context xDrbgContext;
        int lMbedResult;

        /* Initialize the private key. */
        mbedtls_pk_init( &xPkContext );
        lMbedResult = mbedtls_pk_parse_key( &xPkContext,
                                            ( const unsigned char * ) cValidECDSAPrivateKey,
                                            sizeof( cValidECDSAPrivateKey ),
                                            NULL,
                                            0 );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedResult, "Failed to parse valid ECDSA key." );
        /* Initialize the RNG. */
        mbedtls_entropy_init( &xEntropyContext );
        mbedtls_ctr_drbg_init( &xDrbgContext );
        lMbedResult = mbedtls_ctr_drbg_seed( &xDrbgContext, mbedtls_entropy_func, &xEntropyContext, NULL, 0 );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedResult, "Failed to initialize DRBG" );

        lMbedResult = mbedtls_pk_sign( &xPkContext, MBEDTLS_MD_SHA256, xHashedMessage, sizeof( xHashedMessage ), xSignature, &xSignatureLength, mbedtls_ctr_drbg_random, &xDrbgContext );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedResult, "Failed to perform ECDSA signature." );

        mbedtls_pk_free( &xPkContext );
        mbedtls_ctr_drbg_free( &xDrbgContext );
        mbedtls_entropy_free( &xEntropyContext );

        /* Reconstruct the signature in PKCS #11 format. */
        lMbedResult = PKI_mbedTLSSignatureToPkcs11Signature( xSignaturePKCS,
                                                             xSignature );
        TEST_ASSERT_EQUAL_MESSAGE( 0, lMbedResult, "Null buffers." );

        /* Verify with PKCS #11. */
        xMechanism.mechanism = CKM_ECDSA;
        xMechanism.pParameter = NULL;
        xMechanism.ulParameterLen = 0;
        xResult = pxGlobalFunctionList->C_VerifyInit( xGlobalSession, &xMechanism, xPublicKeyHandle );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "VerifyInit failed." );

        xResult = pxGlobalFunctionList->C_Verify( xGlobalSession, xHashedMessage, pkcs11SHA256_DIGEST_LENGTH, xSignaturePKCS, sizeof( xSignaturePKCS ) );
        TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Verify failed." );
    #endif /* if ( pkcs11testIMPORT_PRIVATE_KEY_SUPPORT == 1 ) */
    /* Modify signature value and make sure verification fails. */
}



void test_FindObject_EC( void )
{
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xCertificateHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPublicKeyHandle = CK_INVALID_HANDLE;

    prvFindObjectTest( &xPrivateKeyHandle, &xCertificateHandle, &xPublicKeyHandle );
}

extern int convert_pem_to_der( const unsigned char * pucInput,
                               size_t xLen,
                               unsigned char * pucOutput,
                               size_t * pxOlen );

void test_GetAttributeValue_EC( void )
{
    CK_RV xResult;
    CK_OBJECT_HANDLE xPrivateKey = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPublicKey = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xCertificate = CK_INVALID_HANDLE;
    CK_ATTRIBUTE xTemplate;
    CK_KEY_TYPE xKeyType = 0;
    uint8_t ucP256Oid[] = pkcs11DER_ENCODED_OID_P256;
    CK_BYTE xEcParams[ 10 ] = { 0 };
    CK_OBJECT_CLASS xClass;
    CK_BYTE xEcPointExpected[] =
    {
        0x04, 0x41, 0x04, 0xce, 0x08, 0x69, 0xf9, 0x0b, 0x2d, 0x52, 0x13, 0xa6, 0xcc, 0xa0, 0x46, 0x10,
        0xbe, 0xee, 0x06, 0x3b, 0x1a, 0x05, 0xbc, 0x9a, 0x35, 0x33, 0x0b, 0x5c, 0xa2, 0xd2, 0x5b, 0xbf,
        0x3e, 0x6d, 0xda, 0x0f, 0xf5, 0xb2, 0x93, 0x3a, 0xba, 0xa2, 0x2a, 0x4f, 0x46, 0xcc, 0x59, 0x3d,
        0x0a, 0x1b, 0x61, 0x1c, 0x5b, 0x31, 0xf9, 0x3e, 0xd4, 0x16, 0x2b, 0x61, 0x6d, 0x85, 0xad, 0x45,
        0xfd, 0x19, 0xc3
    };
    CK_BYTE xCertificateValueExpected[ 626 ];
    CK_BYTE xCertificateValue[ 626 ];
    CK_BYTE xEcPoint[ sizeof( xEcPointExpected ) ] = { 0 };
    size_t xLength = sizeof( xCertificateValueExpected );
    int lConversionReturn;

    lConversionReturn = convert_pem_to_der( ( const unsigned char * ) cValidECDSACertificate,
                                            sizeof( cValidECDSACertificate ),
                                            xCertificateValueExpected,
                                            &xLength );

    if( lConversionReturn != 0 )
    {
        LogError( ( "Failed to convert the EC certificate from PEM to DER. Error code %d.", lConversionReturn ) );
    }

    prvFindObjectTest( &xPrivateKey, &xCertificate, &xPublicKey );

    /* The PKCS #11 standard expects that calling GetAttributeValue with a null pointer to the value
     * will yield a success with the value length updated to the size of the buffer needed to contain
     * the attribute.
     *
     * All tests start by querying the attribute length, and followed by a query of the attribute value. */

    /***** Private Key Checks. *****/

    /* Check object class. */
    xTemplate.type = CKA_CLASS;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;

    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of private EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_OBJECT_CLASS ), xTemplate.ulValueLen, "Incorrect object class length returned from GetAttributeValue." );

    xTemplate.pValue = &xClass;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for private EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( CKO_PRIVATE_KEY, xClass, "Incorrect object class returned from GetAttributeValue." );

    /* Key type. */
    xTemplate.type = CKA_KEY_TYPE;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of EC key type failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen, "Incorrect key type length provided." );

    xTemplate.pValue = &xKeyType;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for EC key type failed." );
    TEST_ASSERT_EQUAL_MESSAGE( CKK_EC, xKeyType, "Incorrect key type returned." );

    /* Check EC Params. */
    xTemplate.type = CKA_EC_PARAMS;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of EC params type failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( ucP256Oid ), xTemplate.ulValueLen, "Incorrect EC params length provided." );

    xTemplate.pValue = xEcParams;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for EC params failed." );
    TEST_ASSERT_EQUAL_INT8_ARRAY_MESSAGE( ucP256Oid, xEcParams, sizeof( ucP256Oid ), "Incorrect ECParameters returned from GetAttributeValue" );

    /******* Public Key ********/
    /* Object class. */
    xTemplate.type = CKA_CLASS;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of public EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_OBJECT_CLASS ), xTemplate.ulValueLen, "Incorrect object class length returned from GetAttributeValue." );

    xTemplate.pValue = &xClass;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for public EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( CKO_PUBLIC_KEY, xClass, "Incorrect object class returned from GetAttributeValue." );

    /* Elliptic Curve Parameters (the OID of the curve). At this time only P256 curves are supported. */
    xTemplate.type = CKA_EC_PARAMS;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of public key EC Params failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( ucP256Oid ), xTemplate.ulValueLen, "Incorrect EC params length provided." );

    memset( xEcParams, 0x0, sizeof( ucP256Oid ) );
    xTemplate.pValue = xEcParams;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for EC params failed." );
    TEST_ASSERT_EQUAL_INT8_ARRAY_MESSAGE( ucP256Oid, xEcParams, sizeof( ucP256Oid ), "Incorrect ECParameters returned from GetAttributeValue" );

    /* Elliptic curve point. */
    xTemplate.type = CKA_EC_POINT;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of public key EC point failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( xEcPointExpected ), xTemplate.ulValueLen, "Incorrect EC point length provided." );

    xTemplate.pValue = xEcPoint;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKey, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for EC point failed." );
    #if pkcs11testIMPORT_PRIVATE_KEY_SUPPORT == 1

        /* The EC point can only be known for a public key that was previously created
         * therefore this check is only done for implementations that support importing
         * a private key, as the credentials that are on the device are all known.
         */
        TEST_ASSERT_EQUAL_INT8_ARRAY_MESSAGE( xEcPointExpected, xEcPoint, sizeof( xEcPointExpected ), "Incorrect EC Point returned from GetAttributeValue" );
    #endif

    /****** Certificate check. *******/
    /* Object class. */
    xTemplate.type = CKA_CLASS;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xCertificate, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of EC certificate class failed." );
    #if ( pkcs11testPREPROVISIONED_SUPPORT != 1 )
        TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_OBJECT_CLASS ), xTemplate.ulValueLen, "Incorrect object class length returned from GetAttributeValue." );
    #endif

    xTemplate.pValue = &xClass;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xCertificate, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for EC certificate class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( CKO_CERTIFICATE, xClass, "Incorrect object class returned from GetAttributeValue." );

    /* Certificate value (the DER encoded certificate). */
    xTemplate.type = CKA_VALUE;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xCertificate, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of certificate value failed." );
    #if ( pkcs11testPREPROVISIONED_SUPPORT != 1 )
        TEST_ASSERT_EQUAL_MESSAGE( sizeof( xCertificateValueExpected ), xTemplate.ulValueLen, "Incorrect certificate value length" );
    #endif

    xTemplate.pValue = xCertificateValue;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xCertificate, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for certificate value failed." );
    #if ( pkcs11testPREPROVISIONED_SUPPORT != 1 )
        TEST_ASSERT_EQUAL_INT8_ARRAY_MESSAGE( xCertificateValueExpected, xCertificateValue, sizeof( xCertificateValueExpected ), "Incorrect certificate value returned." );
    #endif
}

/*
 * 1. Generates an Elliptic Curve P256 key pair
 * 2. Calls GetAttributeValue to check generated key & that private key is not extractable.
 * 3. Constructs the public key using values from GetAttributeValue calls
 * 4. Uses private key to perform a sign operation
 * 5. Verifies the signature using mbedTLS library and reconstructed public key
 * 6. Verifies the signature using the public key just created.
 * 7. Finds the public and private key using FindObject calls
 */
void test_GenerateKeyPair_EC( void )
{
    CK_RV xResult;
    CK_OBJECT_HANDLE xPrivateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xPublicKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xCertificateHandle = CK_INVALID_HANDLE;

    CK_BYTE xEcPoint[ 256 ] = { 0 };
    CK_BYTE xPrivateKeyBuffer[ 32 ] = { 0 };
    CK_KEY_TYPE xKeyType;
    CK_ATTRIBUTE xTemplate;
    CK_OBJECT_CLASS xClass;

    /* mbedTLS structures for verification. */
    uint8_t ucSecp256r1Oid[] = pkcs11DER_ENCODED_OID_P256; /*"\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1; */
    CK_BYTE xEcParams[ sizeof( ucSecp256r1Oid ) ] = { 0 };

    xResult = xProvisionGenerateKeyPairEC( xGlobalSession,
                                           ( uint8_t * ) pkcs11testLABEL_DEVICE_PRIVATE_KEY_FOR_TLS,
                                           ( uint8_t * ) pkcs11testLABEL_DEVICE_PUBLIC_KEY_FOR_TLS,
                                           &xPrivateKeyHandle,
                                           &xPublicKeyHandle );

    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Generating EC key pair failed." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xPrivateKeyHandle, "Invalid private key handle generated by GenerateKeyPair" );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xPublicKeyHandle, "Invalid public key handle generated by GenerateKeyPair" );

    /* We will try to provision the certificate as well, as it is needed for the tests that are not responsible for creating objects. */
    xResult = xProvisionCertificate( xGlobalSession,
                                     ( uint8_t * ) cValidECDSACertificate,
                                     sizeof( cValidECDSACertificate ),
                                     ( uint8_t * ) pkcs11testLABEL_DEVICE_CERTIFICATE_FOR_TLS,
                                     &xCertificateHandle );

    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to create EC certificate." );
    TEST_ASSERT_NOT_EQUAL_MESSAGE( CK_INVALID_HANDLE, xCertificateHandle, "Invalid object handle returned for EC certificate." );

    /* Call GetAttributeValue to retrieve information about the keypair stored. */
    /* Check that correct object class retrieved. */
    xTemplate.type = CKA_CLASS;
    xTemplate.pValue = NULL;
    xTemplate.ulValueLen = 0;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for length of public EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_OBJECT_CLASS ), xTemplate.ulValueLen, "Incorrect object class length returned from GetAttributeValue." );

    xTemplate.pValue = &xClass;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for private EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( CKO_PRIVATE_KEY, xClass, "Incorrect object class returned from GetAttributeValue." );

    xTemplate.pValue = &xClass;
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "GetAttributeValue for public EC key class failed." );
    TEST_ASSERT_EQUAL_MESSAGE( CKO_PUBLIC_KEY, xClass, "Incorrect object class returned from GetAttributeValue." );

    /* Check that both keys are stored as EC Keys. */
    xTemplate.type = CKA_KEY_TYPE;
    xTemplate.pValue = &xKeyType;
    xTemplate.ulValueLen = sizeof( CK_KEY_TYPE );
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Error getting attribute value of EC key type." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen, "Length of key type incorrect in GetAttributeValue" );
    TEST_ASSERT_EQUAL_MESSAGE( CKK_EC, xKeyType, "Incorrect key type for private key" );

    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Error getting attribute value of EC key type." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen, "Length of key type incorrect in GetAttributeValue" );
    TEST_ASSERT_EQUAL_MESSAGE( CKK_EC, xKeyType, "Incorrect key type for public key" );

    /* Check that correct curve retrieved for private key. */
    xTemplate.type = CKA_EC_PARAMS;
    xTemplate.pValue = xEcParams;
    xTemplate.ulValueLen = sizeof( xEcParams );
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Error getting attribute value of EC Parameters." );
    TEST_ASSERT_EQUAL_MESSAGE( sizeof( ucSecp256r1Oid ), xTemplate.ulValueLen, "Length of ECParameters identifier incorrect in GetAttributeValue" );
    TEST_ASSERT_EQUAL_INT8_ARRAY_MESSAGE( ucSecp256r1Oid, xEcParams, xTemplate.ulValueLen, "EcParameters did not match P256 OID." );

    /* Check that the private key cannot be retrieved. */
    xTemplate.type = CKA_VALUE;
    xTemplate.pValue = xPrivateKeyBuffer;
    xTemplate.ulValueLen = sizeof( xPrivateKeyBuffer );
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPrivateKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_ATTRIBUTE_SENSITIVE, xResult, "Wrong error code retrieving private key" );
    TEST_ASSERT_EACH_EQUAL_INT8_MESSAGE( 0, xPrivateKeyBuffer, sizeof( xPrivateKeyBuffer ), "Private key bytes returned when they should not be" );

    /* Check that public key point can be retrieved for public key. */
    xTemplate.type = CKA_EC_POINT;
    xTemplate.pValue = xEcPoint;
    xTemplate.ulValueLen = sizeof( xEcPoint );
    xResult = pxGlobalFunctionList->C_GetAttributeValue( xGlobalSession, xPublicKeyHandle, &xTemplate, 1 );
    TEST_ASSERT_EQUAL_MESSAGE( CKR_OK, xResult, "Failed to retrieve EC Point." );
}

/*-----------------------------------------------------------*/

/* Import the specified ECDSA private key into storage. */
static CK_RV prvProvisionPrivateECKey( CK_SESSION_HANDLE xSession,
                                       uint8_t * pucLabel,
                                       CK_OBJECT_HANDLE_PTR pxObjectHandle,
                                       mbedtls_pk_context * pxMbedPkContext )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_BYTE * pxD;               /* Private value D. */
    CK_BYTE * pxEcParams = NULL; /* DER-encoding of an ANSI X9.62 Parameters value */
    int lMbedResult = 0;
    CK_BBOOL xTrue = CK_TRUE;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    mbedtls_ecp_keypair * pxKeyPair = ( mbedtls_ecp_keypair * ) pxMbedPkContext->pk_ctx;

    xResult = C_GetFunctionList( &pxFunctionList );

    pxD = PKCS11_MALLOC( EC_D_LENGTH );

    if( ( pxD == NULL ) )
    {
        xResult = CKR_HOST_MEMORY;
    }

    if( xResult == CKR_OK )
    {
        lMbedResult = mbedtls_mpi_write_binary( &( pxKeyPair->d ), pxD, EC_D_LENGTH );

        if( lMbedResult != 0 )
        {
            LogError( ( "Failed to parse EC private key components. \r\n" ) );
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        if( pxKeyPair->grp.id == MBEDTLS_ECP_DP_SECP256R1 )
        {
            pxEcParams = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
        }
        else
        {
            xResult = CKR_CURVE_NOT_SUPPORTED;
        }
    }

    if( xResult == CKR_OK )
    {
        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_CLASS,     NULL /* &xPrivateKeyClass*/, sizeof( CK_OBJECT_CLASS )                        },
            { CKA_KEY_TYPE,  NULL /* &xPrivateKeyType*/,  sizeof( CK_KEY_TYPE )                            },
            { CKA_LABEL,     pucLabel,                    ( CK_ULONG ) strlen( ( const char * ) pucLabel ) },
            { CKA_TOKEN,     NULL /* &xTrue*/,            sizeof( CK_BBOOL )                               },
            { CKA_SIGN,      NULL /* &xTrue*/,            sizeof( CK_BBOOL )                               },
            { CKA_EC_PARAMS, NULL /* pxEcParams*/,        EC_PARAMS_LENGTH                                 },
            { CKA_VALUE,     NULL /* pxD*/,               EC_D_LENGTH                                      }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        /* See MSVC Compiler Warning C4221 */
        xPrivateKeyTemplate[ 0 ].pValue = &xPrivateKeyClass;
        xPrivateKeyTemplate[ 1 ].pValue = &xPrivateKeyType;
        xPrivateKeyTemplate[ 3 ].pValue = &xTrue;
        xPrivateKeyTemplate[ 4 ].pValue = &xTrue;
        xPrivateKeyTemplate[ 5 ].pValue = pxEcParams;
        xPrivateKeyTemplate[ 6 ].pValue = pxD;

        xResult = pxFunctionList->C_CreateObject( xSession,
                                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  pxObjectHandle );
    }

    if( pxD != NULL )
    {
        PKCS11_FREE( pxD );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

/* Import the specified RSA private key into storage. */
static CK_RV prvProvisionPrivateRSAKey( CK_SESSION_HANDLE xSession,
                                        uint8_t * pucLabel,
                                        CK_OBJECT_HANDLE_PTR pxObjectHandle,
                                        mbedtls_pk_context * pxMbedPkContext )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    int lMbedResult = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_RSA;
    mbedtls_rsa_context * xRsaContext = pxMbedPkContext->pk_ctx;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    RsaParams_t * pxRsaParams = NULL;
    CK_BBOOL xTrue = CK_TRUE;

    xResult = C_GetFunctionList( &pxFunctionList );

    pxRsaParams = PKCS11_MALLOC( sizeof( RsaParams_t ) );

    if( pxRsaParams == NULL )
    {
        xResult = CKR_HOST_MEMORY;
    }

    if( xResult == CKR_OK )
    {
        memset( pxRsaParams, 0, sizeof( RsaParams_t ) );

        lMbedResult = mbedtls_rsa_export_raw( xRsaContext,
                                              pxRsaParams->modulus, MODULUS_LENGTH + 1,
                                              pxRsaParams->prime1, PRIME_1_LENGTH + 1,
                                              pxRsaParams->prime2, PRIME_2_LENGTH + 1,
                                              pxRsaParams->d, D_LENGTH + 1,
                                              pxRsaParams->e, E_LENGTH + 1 );

        if( lMbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key components. \r\n" ) );
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }

        /* Export Exponent 1, Exponent 2, Coefficient. */
        lMbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &xRsaContext->DP, pxRsaParams->exponent1, EXPONENT_1_LENGTH + 1 );
        lMbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &xRsaContext->DQ, pxRsaParams->exponent2, EXPONENT_2_LENGTH + 1 );
        lMbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &xRsaContext->QP, pxRsaParams->coefficient, COEFFICIENT_LENGTH + 1 );

        if( lMbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key Chinese Remainder Theorem variables. \r\n" ) );
            xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( xResult == CKR_OK )
    {
        /* When importing the fields, the pointer is incremented by 1
         * to remove the leading 0 padding (if it existed) and the original field length is used */


        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_CLASS,            NULL /* &xPrivateKeyClass */, sizeof( CK_OBJECT_CLASS )                        },
            { CKA_KEY_TYPE,         NULL /* &xPrivateKeyType */,  sizeof( CK_KEY_TYPE )                            },
            { CKA_LABEL,            pucLabel,                     ( CK_ULONG ) strlen( ( const char * ) pucLabel ) },
            { CKA_TOKEN,            NULL /* &xTrue */,            sizeof( CK_BBOOL )                               },
            { CKA_SIGN,             NULL /* &xTrue */,            sizeof( CK_BBOOL )                               },
            { CKA_MODULUS,          pxRsaParams->modulus + 1,     MODULUS_LENGTH                                   },
            { CKA_PRIVATE_EXPONENT, pxRsaParams->d + 1,           D_LENGTH                                         },
            { CKA_PUBLIC_EXPONENT,  pxRsaParams->e + 1,           E_LENGTH                                         },
            { CKA_PRIME_1,          pxRsaParams->prime1 + 1,      PRIME_1_LENGTH                                   },
            { CKA_PRIME_2,          pxRsaParams->prime2 + 1,      PRIME_2_LENGTH                                   },
            { CKA_EXPONENT_1,       pxRsaParams->exponent1 + 1,   EXPONENT_1_LENGTH                                },
            { CKA_EXPONENT_2,       pxRsaParams->exponent2 + 1,   EXPONENT_2_LENGTH                                },
            { CKA_COEFFICIENT,      pxRsaParams->coefficient + 1, COEFFICIENT_LENGTH                               }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        /* See MSVC Compiler Warning C4221 */
        xPrivateKeyTemplate[ 0 ].pValue = &xPrivateKeyClass;
        xPrivateKeyTemplate[ 1 ].pValue = &xPrivateKeyType;
        xPrivateKeyTemplate[ 3 ].pValue = &xTrue;
        xPrivateKeyTemplate[ 4 ].pValue = &xTrue;

        xResult = pxFunctionList->C_CreateObject( xSession,
                                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  pxObjectHandle );
    }

    if( NULL != pxRsaParams )
    {
        PKCS11_FREE( pxRsaParams );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

/* Import the specified private key into storage. */
CK_RV xProvisionPrivateKey( CK_SESSION_HANDLE xSession,
                            uint8_t * pucPrivateKey,
                            size_t xPrivateKeyLength,
                            uint8_t * pucLabel,
                            CK_OBJECT_HANDLE_PTR pxObjectHandle )
{
    CK_RV xResult = CKR_OK;
    mbedtls_pk_type_t xMbedKeyType = MBEDTLS_PK_NONE;
    int lMbedResult = 0;
    mbedtls_pk_context xMbedPkContext = { 0 };

    mbedtls_pk_init( &xMbedPkContext );
    lMbedResult = mbedtls_pk_parse_key( &xMbedPkContext, pucPrivateKey, xPrivateKeyLength, NULL, 0 );

    if( lMbedResult != 0 )
    {
        LogError( ( "Unable to parse private key.\r\n" ) );
        xResult = CKR_ARGUMENTS_BAD;
    }

    /* Determine whether the key to be imported is RSA or EC. */
    if( xResult == CKR_OK )
    {
        xMbedKeyType = mbedtls_pk_get_type( &xMbedPkContext );

        if( xMbedKeyType == MBEDTLS_PK_RSA )
        {
            xResult = prvProvisionPrivateRSAKey( xSession,
                                                 pucLabel,
                                                 pxObjectHandle,
                                                 &xMbedPkContext );
        }
        else if( ( xMbedKeyType == MBEDTLS_PK_ECDSA ) || ( xMbedKeyType == MBEDTLS_PK_ECKEY ) || ( xMbedKeyType == MBEDTLS_PK_ECKEY_DH ) )
        {
            xResult = prvProvisionPrivateECKey( xSession,
                                                pucLabel,
                                                pxObjectHandle,
                                                &xMbedPkContext );
        }
        else
        {
            LogError( ( "Invalid private key type provided.  RSA-2048 and EC P-256 keys are supported.\r\n" ) );
            xResult = CKR_ARGUMENTS_BAD;
        }
    }

    mbedtls_pk_free( &xMbedPkContext );

    return xResult;
}

/*-----------------------------------------------------------*/

/* Import the specified public key into storage. */
CK_RV xProvisionPublicKey( CK_SESSION_HANDLE xSession,
                           uint8_t * pucKey,
                           size_t xKeyLength,
                           CK_KEY_TYPE xPublicKeyType,
                           uint8_t * pucPublicKeyLabel,
                           CK_OBJECT_HANDLE_PTR pxPublicKeyHandle )
{
    CK_RV xResult;
    CK_BBOOL xTrue = CK_TRUE;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_OBJECT_CLASS xClass = CKO_PUBLIC_KEY;
    int lMbedResult = 0;
    mbedtls_pk_context xMbedPkContext = { 0 };

    xResult = C_GetFunctionList( &pxFunctionList );

    mbedtls_pk_init( &xMbedPkContext );

    /* Try parsing the private key using mbedtls_pk_parse_key. */
    lMbedResult = mbedtls_pk_parse_key( &xMbedPkContext, pucKey, xKeyLength, NULL, 0 );

    /* If mbedtls_pk_parse_key didn't work, maybe the private key is not included in the input passed in.
     * Try to parse just the public key. */
    if( lMbedResult != 0 )
    {
        lMbedResult = mbedtls_pk_parse_public_key( &xMbedPkContext, pucKey, xKeyLength );
    }

    if( lMbedResult != 0 )
    {
        LogError( ( "Failed to parse the public key. \r\n" ) );
        xResult = CKR_ARGUMENTS_BAD;
    }

    if( ( xResult == CKR_OK ) && ( xPublicKeyType == CKK_RSA ) )
    {
        CK_BYTE xPublicExponent[] = { 0x01, 0x00, 0x01 };
        CK_BYTE xModulus[ MODULUS_LENGTH + 1 ] = { 0 };

        lMbedResult = mbedtls_rsa_export_raw( ( mbedtls_rsa_context * ) xMbedPkContext.pk_ctx,
                                              ( unsigned char * ) &xModulus, MODULUS_LENGTH + 1,
                                              NULL, 0,
                                              NULL, 0,
                                              NULL, 0,
                                              NULL, 0 );
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_CLASS,           NULL /* &xClass */,         sizeof( CK_OBJECT_CLASS )                    },
            { CKA_KEY_TYPE,        NULL /* &xPublicKeyType */, sizeof( CK_KEY_TYPE )                        },
            { CKA_TOKEN,           NULL /* &xTrue */,          sizeof( xTrue )                              },
            { CKA_MODULUS,         NULL /* &xModulus + 1 */,   MODULUS_LENGTH                               },       /* Extra byte allocated at beginning for 0 padding. */
            { CKA_VERIFY,          NULL /* &xTrue */,          sizeof( xTrue )                              },
            { CKA_PUBLIC_EXPONENT, NULL /* xPublicExponent */, sizeof( xPublicExponent )                    },
            { CKA_LABEL,           pucPublicKeyLabel,          strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        /* See MSVC Compiler Warning C4221 */
        xPublicKeyTemplate[ 0 ].pValue = &xClass;
        xPublicKeyTemplate[ 1 ].pValue = &xPublicKeyType;
        xPublicKeyTemplate[ 2 ].pValue = &xTrue;
        xPublicKeyTemplate[ 3 ].pValue = &xModulus + 1;
        xPublicKeyTemplate[ 4 ].pValue = &xTrue;
        xPublicKeyTemplate[ 5 ].pValue = xPublicExponent;

        xResult = pxFunctionList->C_CreateObject( xSession,
                                                  ( CK_ATTRIBUTE_PTR ) xPublicKeyTemplate,
                                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  pxPublicKeyHandle );
    }
    else if( ( xResult == CKR_OK ) && ( xPublicKeyType == CKK_EC ) )
    {
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256;
        size_t xLength;
        CK_BYTE xEcPoint[ 256 ] = { 0 };

        mbedtls_ecdsa_context * pxEcdsaContext = ( mbedtls_ecdsa_context * ) xMbedPkContext.pk_ctx;

        /* DER encoded EC point. Leave 2 bytes for the tag and length. */
        lMbedResult = mbedtls_ecp_point_write_binary( &pxEcdsaContext->grp,
                                                      &pxEcdsaContext->Q,
                                                      MBEDTLS_ECP_PF_UNCOMPRESSED,
                                                      &xLength,
                                                      xEcPoint + 2,
                                                      sizeof( xEcPoint ) - 2 );
        xEcPoint[ 0 ] = 0x04; /* Octet string. */
        xEcPoint[ 1 ] = ( CK_BYTE ) xLength;

        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_CLASS,     NULL /* &xClass */,         sizeof( xClass )                             },
            { CKA_KEY_TYPE,  NULL /* &xPublicKeyType */, sizeof( xPublicKeyType )                     },
            { CKA_TOKEN,     NULL /* &xTrue */,          sizeof( xTrue )                              },
            { CKA_VERIFY,    NULL /* &xTrue */,          sizeof( xTrue )                              },
            { CKA_EC_PARAMS, NULL /* xEcParams */,       sizeof( xEcParams )                          },
            { CKA_EC_POINT,  NULL /* xEcPoint */,        xLength + 2                                  },
            { CKA_LABEL,     pucPublicKeyLabel,          strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        /* See MSVC Compiler Warning C4221 */
        xPublicKeyTemplate[ 0 ].pValue = &xClass;
        xPublicKeyTemplate[ 1 ].pValue = &xPublicKeyType;
        xPublicKeyTemplate[ 2 ].pValue = &xTrue;
        xPublicKeyTemplate[ 3 ].pValue = &xTrue;
        xPublicKeyTemplate[ 4 ].pValue = xEcParams;
        xPublicKeyTemplate[ 5 ].pValue = xEcPoint;

        xResult = pxFunctionList->C_CreateObject( xSession,
                                                  ( CK_ATTRIBUTE_PTR ) xPublicKeyTemplate,
                                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  pxPublicKeyHandle );
    }
    else
    {
        xResult = CKR_ATTRIBUTE_VALUE_INVALID;
        LogError( ( "Invalid key type. Supported options are CKK_RSA and CKK_EC" ) );
    }

    mbedtls_pk_free( &xMbedPkContext );

    return xResult;
}

/*-----------------------------------------------------------*/

/* Generate a new ECDSA key pair using curve P256. */
CK_RV xProvisionGenerateKeyPairEC( CK_SESSION_HANDLE xSession,
                                   uint8_t * pucPrivateKeyLabel,
                                   uint8_t * pucPublicKeyLabel,
                                   CK_OBJECT_HANDLE_PTR pxPrivateKeyHandle,
                                   CK_OBJECT_HANDLE_PTR pxPublicKeyHandle )
{
    CK_RV xResult;
    CK_MECHANISM xMechanism =
    {
        CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
    };
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
    CK_KEY_TYPE xKeyType = CKK_EC;

    CK_BBOOL xTrue = CK_TRUE;
    CK_ATTRIBUTE xPublicKeyTemplate[] =
    {
        { CKA_KEY_TYPE,  NULL /* &xKeyType */, sizeof( xKeyType )                           },
        { CKA_VERIFY,    NULL /* &xTrue */,    sizeof( xTrue )                              },
        { CKA_EC_PARAMS, NULL /* xEcParams */, sizeof( xEcParams )                          },
        { CKA_LABEL,     pucPublicKeyLabel,    strlen( ( const char * ) pucPublicKeyLabel ) }
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    /* See MSVC Compiler Warning C4221 */
    xPublicKeyTemplate[ 0 ].pValue = &xKeyType;
    xPublicKeyTemplate[ 1 ].pValue = &xTrue;
    xPublicKeyTemplate[ 2 ].pValue = &xEcParams;

    CK_ATTRIBUTE xPrivateKeyTemplate[] =
    {
        { CKA_KEY_TYPE, NULL /* &xKeyType */, sizeof( xKeyType )                            },
        { CKA_TOKEN,    NULL /* &xTrue */,    sizeof( xTrue )                               },
        { CKA_PRIVATE,  NULL /* &xTrue */,    sizeof( xTrue )                               },
        { CKA_SIGN,     NULL /* &xTrue */,    sizeof( xTrue )                               },
        { CKA_LABEL,    pucPrivateKeyLabel,   strlen( ( const char * ) pucPrivateKeyLabel ) }
    };

    /* Aggregate initializers must not use the address of an automatic variable. */
    /* See MSVC Compiler Warning C4221 */
    xPrivateKeyTemplate[ 0 ].pValue = &xKeyType;
    xPrivateKeyTemplate[ 1 ].pValue = &xTrue;
    xPrivateKeyTemplate[ 2 ].pValue = &xTrue;
    xPrivateKeyTemplate[ 3 ].pValue = &xTrue;

    xResult = C_GetFunctionList( &pxFunctionList );

    xResult = pxFunctionList->C_GenerateKeyPair( xSession,
                                                 &xMechanism,
                                                 xPublicKeyTemplate,
                                                 sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                 xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                 pxPublicKeyHandle,
                                                 pxPrivateKeyHandle );

    return xResult;
}

/*-----------------------------------------------------------*/

/* Import the specified X.509 client certificate into storage. */
CK_RV xProvisionCertificate( CK_SESSION_HANDLE xSession,
                             uint8_t * pucCertificate,
                             size_t xCertificateLength,
                             uint8_t * pucLabel,
                             CK_OBJECT_HANDLE_PTR pxObjectHandle )
{
    PKCS11_CertificateTemplate_t xCertificateTemplate;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_RV xResult;
    uint8_t * pucDerObject = NULL;
    int32_t lConversionReturn = 0;
    size_t xDerLen = 0;
    CK_BBOOL xTokenStorage = CK_TRUE;

    /* TODO: Subject is a required attribute.
     * Currently, this field is not used by FreeRTOS ports,
     * this should be updated so that subject matches proper
     * format for future ports. */
    CK_BYTE xSubject[] = "TestSubject";

    /* Initialize the client certificate template. */
    xCertificateTemplate.xObjectClass.type = CKA_CLASS;
    xCertificateTemplate.xObjectClass.pValue = &xCertificateClass;
    xCertificateTemplate.xObjectClass.ulValueLen = sizeof( xCertificateClass );
    xCertificateTemplate.xSubject.type = CKA_SUBJECT;
    xCertificateTemplate.xSubject.pValue = xSubject;
    xCertificateTemplate.xSubject.ulValueLen = strlen( ( const char * ) xSubject );
    xCertificateTemplate.xValue.type = CKA_VALUE;
    xCertificateTemplate.xValue.pValue = ( CK_VOID_PTR ) pucCertificate;
    xCertificateTemplate.xValue.ulValueLen = ( CK_ULONG ) xCertificateLength;
    xCertificateTemplate.xLabel.type = CKA_LABEL;
    xCertificateTemplate.xLabel.pValue = ( CK_VOID_PTR ) pucLabel;
    xCertificateTemplate.xLabel.ulValueLen = strlen( ( const char * ) pucLabel );
    xCertificateTemplate.xCertificateType.type = CKA_CERTIFICATE_TYPE;
    xCertificateTemplate.xCertificateType.pValue = &xCertificateType;
    xCertificateTemplate.xCertificateType.ulValueLen = sizeof( CK_CERTIFICATE_TYPE );
    xCertificateTemplate.xTokenObject.type = CKA_TOKEN;
    xCertificateTemplate.xTokenObject.pValue = &xTokenStorage;
    xCertificateTemplate.xTokenObject.ulValueLen = sizeof( xTokenStorage );

    xResult = C_GetFunctionList( &pxFunctionList );

    /* Test for a valid certificate: 0x2d is '-', as in ----- BEGIN CERTIFICATE. */
    if( ( pucCertificate == NULL ) || ( pucCertificate[ 0 ] != 0x2d ) )
    {
        xResult = CKR_ATTRIBUTE_VALUE_INVALID;
    }

    if( xResult == CKR_OK )
    {
        /* Convert the certificate to DER format if it was in PEM. The DER key
         * should be about 3/4 the size of the PEM key, so mallocing the PEM key
         * size is sufficient. */
        pucDerObject = PKCS11_MALLOC( xCertificateTemplate.xValue.ulValueLen );
        xDerLen = xCertificateTemplate.xValue.ulValueLen;

        if( pucDerObject != NULL )
        {
            lConversionReturn = convert_pem_to_der( xCertificateTemplate.xValue.pValue,
                                                    xCertificateTemplate.xValue.ulValueLen,
                                                    pucDerObject,
                                                    &xDerLen );

            if( 0 != lConversionReturn )
            {
                xResult = CKR_ARGUMENTS_BAD;
            }
        }
        else
        {
            xResult = CKR_HOST_MEMORY;
        }
    }

    if( xResult == CKR_OK )
    {
        /* Set the template pointers to refer to the DER converted objects. */
        xCertificateTemplate.xValue.pValue = pucDerObject;
        xCertificateTemplate.xValue.ulValueLen = xDerLen;
    }

    /* Best effort clean-up of the existing object, if it exists. */
    if( xResult == CKR_OK )
    {
        xDestroyProvidedObjects( xSession,
                                 &pucLabel,
                                 &xCertificateClass,
                                 1 );
    }

    /* Create an object using the encoded client certificate. */
    if( xResult == CKR_OK )
    {
        LogError( ( "Write certificate...\r\n" ) );

        xResult = pxFunctionList->C_CreateObject( xSession,
                                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  pxObjectHandle );
    }

    if( pucDerObject != NULL )
    {
        PKCS11_FREE( pucDerObject );
    }

    return xResult;
}

/*-----------------------------------------------------------*/

/* Delete the specified crypto object from storage. */
CK_RV xDestroyProvidedObjects( CK_SESSION_HANDLE xSession,
                               CK_BYTE_PTR * ppxPkcsLabels,
                               CK_OBJECT_CLASS * xClass,
                               CK_ULONG ulCount )
{
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_OBJECT_HANDLE xObjectHandle;
    CK_BYTE * pxLabel;
    CK_ULONG uiIndex = 0;

    xResult = C_GetFunctionList( &pxFunctionList );

    for( uiIndex = 0; uiIndex < ulCount; uiIndex++ )
    {
        pxLabel = ppxPkcsLabels[ uiIndex ];

        xResult = xFindObjectWithLabelAndClass( xSession,
                                                ( char * ) pxLabel,
                                                xClass[ uiIndex ],
                                                &xObjectHandle );

        while( ( xResult == CKR_OK ) && ( xObjectHandle != CK_INVALID_HANDLE ) )
        {
            xResult = pxFunctionList->C_DestroyObject( xSession, xObjectHandle );

            /* PKCS #11 allows a module to maintain multiple objects with the same
             * label and type. The intent of this loop is to try to delete all of them.
             * However, to avoid getting stuck, we won't try to find another object
             * of the same label/type if the previous delete failed. */
            if( xResult == CKR_OK )
            {
                xResult = xFindObjectWithLabelAndClass( xSession,
                                                        ( char * ) pxLabel,
                                                        xClass[ uiIndex ],
                                                        &xObjectHandle );
            }
            else
            {
                break;
            }
        }

        if( xResult == CKR_FUNCTION_NOT_SUPPORTED )
        {
            break;
        }
    }

    return xResult;
}

/*-----------------------------------------------------------*/
