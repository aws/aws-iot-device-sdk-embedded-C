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

/**
 * @file demo_helpers.c
 * @brief Common functions used between the PKCS #11 demos.
 */
/* Standard includes. */
#include <stdio.h>
#include <assert.h>

/* PKCS #11 includes. */
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"
#include "pkcs11.h"

/* mbed TLS includes. */
#include "mbedtls/pk.h"
#include "mbedtls/oid.h"

/* Helpers include. */
#include "demo_helpers.h"


/*
 * @brief macro to help print public key hex to serial.
 */
#define BYTES_TO_DISPLAY_PER_ROW    16
/*-----------------------------------------------------------*/

void vStart( CK_SESSION_HANDLE * pxSession,
             CK_SLOT_ID ** ppxSlotId )
{
    CK_RV xResult = CKR_OK;

    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;
    CK_C_INITIALIZE_ARGS xInitArgs = { 0 };
    CK_SESSION_HANDLE hSession = CK_INVALID_HANDLE;
    CK_ULONG xSlotCount = 0;
    CK_SLOT_ID * pxSlotId = NULL;

    xResult = C_GetFunctionList( &pxFunctionList );
    assert( xResult == CKR_OK );
    assert( pxFunctionList != NULL );
    assert( pxFunctionList->C_Initialize != NULL );
    assert( pxFunctionList->C_GetSlotList != NULL );
    assert( pxFunctionList->C_OpenSession != NULL );
    assert( pxFunctionList->C_Login != NULL );
    assert( pxFunctionList->C_GenerateRandom != NULL );
    assert( pxFunctionList->C_CloseSession != NULL );
    assert( pxFunctionList->C_Finalize != NULL );

    xResult = pxFunctionList->C_Initialize( &xInitArgs );
    assert( xResult == CKR_OK );

    xResult = pxFunctionList->C_GetSlotList( CK_TRUE,
                                             NULL,
                                             &xSlotCount );
    assert( xResult == CKR_OK );

    pxSlotId = PKCS11_MALLOC( sizeof( CK_SLOT_ID ) * ( xSlotCount ) );
    assert( pxSlotId != NULL );

    xResult = pxFunctionList->C_GetSlotList( CK_TRUE,
                                             pxSlotId,
                                             &xSlotCount );
    assert( xResult == CKR_OK );

    xResult = pxFunctionList->C_OpenSession( pxSlotId[ 0 ],
                                             CKF_SERIAL_SESSION | CKF_RW_SESSION,
                                             NULL, /* Application defined pointer. */
                                             NULL, /* Callback function. */
                                             &hSession );
    assert( xResult == CKR_OK );


    xResult = pxFunctionList->C_Login( hSession,
                                       CKU_USER,
                                       ( CK_UTF8CHAR_PTR ) configPKCS11_DEFAULT_USER_PIN,
                                       sizeof( configPKCS11_DEFAULT_USER_PIN ) - 1UL );
    assert( xResult == CKR_OK );

    *ppxSlotId = pxSlotId;
    *pxSession = hSession;

    /* To avoid warnings if asserts are disabled. */
    ( void ) xResult;
}
/*-----------------------------------------------------------*/

void vEnd( CK_SESSION_HANDLE xSession,
           CK_SLOT_ID * pxSlotId )
{
    C_CloseSession( xSession );
    C_Finalize( NULL );
    PKCS11_FREE( pxSlotId );
}
/*-----------------------------------------------------------*/

void vWriteHexBytesToConsole( char * pcDescription,
                              CK_BYTE * pucData,
                              CK_ULONG ulDataLength )
{
    /* This function is simply a helper function to print the raw hex values
     * of an EC public key. It's explanation is not within the scope of the demos
     * and is sparsely commented. */
    char pcByteRow[ 1 + ( BYTES_TO_DISPLAY_PER_ROW * 2 ) + ( BYTES_TO_DISPLAY_PER_ROW / 2 ) ];
    char * pcNextChar = pcByteRow;
    uint32_t ulIndex = 0;
    uint8_t ucByteValue = 0;

    ( void ) pcDescription;

    /* Write help text to the console. */
    LogInfo( ( "%s, %lu bytes:", pcDescription, ulDataLength ) );

    /* Iterate over the bytes of the encoded public key. */
    for( ulIndex = 0; ulIndex < ulDataLength; ulIndex++ )
    {
        /* Convert one byte to ASCII hex. */
        ucByteValue = *( pucData + ulIndex );
        snprintf( pcNextChar,
                  sizeof( pcByteRow ) - ( pcNextChar - pcByteRow ),
                  "%02x",
                  ucByteValue );
        pcNextChar += 2;

        /* Check for the end of a two-byte display word. */
        if( 0 == ( ( ulIndex + 1 ) % sizeof( uint16_t ) ) )
        {
            *pcNextChar = ' ';
            pcNextChar++;
        }

        /* Check for the end of a row. */
        if( 0 == ( ( ulIndex + 1 ) % BYTES_TO_DISPLAY_PER_ROW ) )
        {
            *pcNextChar = '\0';
            LogInfo( ( "%s", pcByteRow ) );
            pcNextChar = pcByteRow;
        }
    }

    /* Check for a partial line to print. */
    if( pcNextChar > pcByteRow )
    {
        *pcNextChar = '\0';
        LogInfo( ( "%s", pcByteRow ) );
    }
}
/*-----------------------------------------------------------*/

CK_RV vExportPublicKey( CK_SESSION_HANDLE xSession,
                        CK_OBJECT_HANDLE xPublicKeyHandle,
                        CK_BYTE ** ppucDerPublicKey,
                        CK_ULONG * pulDerPublicKeyLength )
{
    /* This function is simply a helper function to export the raw hex values
     * of an EC public key into a buffer. It's explanation is not within the
     * scope of the demos and is sparsely commented. */
    CK_RV xResult;
    CK_FUNCTION_LIST_PTR pxFunctionList;
    CK_KEY_TYPE xKeyType = 0;
    CK_ATTRIBUTE xTemplate = { 0 };
    uint8_t pucEcP256AsnAndOid[] =
    {
        0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86,
        0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a,
        0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03,
        0x42, 0x00
    };
    uint8_t pucUnusedKeyTag[] = { 0x04, 0x41 };

    /* This variable is used only for its size. This gets rid of compiler warnings. */
    ( void ) pucUnusedKeyTag;

    xResult = C_GetFunctionList( &pxFunctionList );

    /* Query the key type. */
    if( CKR_OK == xResult )
    {
        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = &xKeyType;
        xTemplate.ulValueLen = sizeof( xKeyType );
        xResult = pxFunctionList->C_GetAttributeValue( xSession,
                                                       xPublicKeyHandle,
                                                       &xTemplate,
                                                       1 );
    }

    /* Scope to ECDSA keys only, since there's currently no use case for
     * onboard keygen and certificate enrollment for RSA. */
    if( ( CKR_OK == xResult ) && ( CKK_ECDSA == xKeyType ) )
    {
        /* Query the size of the public key. */
        xTemplate.type = CKA_EC_POINT;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;
        xResult = pxFunctionList->C_GetAttributeValue( xSession,
                                                       xPublicKeyHandle,
                                                       &xTemplate,
                                                       1 );

        /* Allocate a buffer large enough for the full, encoded public key. */
        if( CKR_OK == xResult )
        {
            /* Add space for the full DER header. */
            xTemplate.ulValueLen += sizeof( pucEcP256AsnAndOid ) - sizeof( pucUnusedKeyTag );
            *pulDerPublicKeyLength = xTemplate.ulValueLen;

            /* Get a heap buffer. */
            *ppucDerPublicKey = PKCS11_MALLOC( xTemplate.ulValueLen );

            /* Check for resource exhaustion. */
            if( NULL == *ppucDerPublicKey )
            {
                xResult = CKR_HOST_MEMORY;
            }
        }

        /* Export the public key. */
        if( CKR_OK == xResult )
        {
            xTemplate.pValue = *ppucDerPublicKey + sizeof( pucEcP256AsnAndOid ) - sizeof( pucUnusedKeyTag );
            xTemplate.ulValueLen -= ( sizeof( pucEcP256AsnAndOid ) - sizeof( pucUnusedKeyTag ) );
            xResult = pxFunctionList->C_GetAttributeValue( xSession,
                                                           xPublicKeyHandle,
                                                           &xTemplate,
                                                           1 );
        }

        /* Prepend the full DER header. */
        if( CKR_OK == xResult )
        {
            memcpy( *ppucDerPublicKey, pucEcP256AsnAndOid, sizeof( pucEcP256AsnAndOid ) );
        }
    }

    /* Free memory if there was an error after allocation. */
    if( ( NULL != *ppucDerPublicKey ) && ( CKR_OK != xResult ) )
    {
        PKCS11_FREE( *ppucDerPublicKey );
        *ppucDerPublicKey = NULL;
    }

    return xResult;
}
/*-----------------------------------------------------------*/
