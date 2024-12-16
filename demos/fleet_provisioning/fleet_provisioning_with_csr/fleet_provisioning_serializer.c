/*
 * AWS IoT Device SDK for Embedded C 202412.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/* Standard includes */
#include <stdarg.h>

/* TinyCBOR library for CBOR encoding and decoding operations. */
#include "cbor.h"

/* Demo config. */
#include "demo_config.h"

/* AWS IoT Fleet Provisioning Library. */
#include "fleet_provisioning.h"

/* Header include. */
#include "fleet_provisioning_serializer.h"

/*-----------------------------------------------------------*/

/**
 * @brief Context passed to tinyCBOR for #cborPrinter. Initial
 * state should be zeroed.
 */
typedef struct
{
    const char * str;
    size_t length;
} CborPrintContext_t;

/*-----------------------------------------------------------*/

/**
 * @brief Printing function to pass to tinyCBOR.
 *
 * cbor_value_to_pretty_stream calls it multiple times to print a textual CBOR
 * representation.
 *
 * @param token Context for the function.
 * @param fmt Printf style format string.
 * @param ... Printf style args after format string.
 */
static CborError cborPrinter( void * token,
                              const char * fmt,
                              ... );

/*-----------------------------------------------------------*/

bool generateCsrRequest( uint8_t * pBuffer,
                         size_t bufferLength,
                         const char * pCsr,
                         size_t csrLength,
                         size_t * pOutLengthWritten )
{
    CborEncoder encoder, mapEncoder;
    CborError cborRet;

    assert( pBuffer != NULL );
    assert( pCsr != NULL );
    assert( pOutLengthWritten != NULL );

    /* For details on the CreateCertificatefromCsr request payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#create-cert-csr-request-payload
     */
    cbor_encoder_init( &encoder, pBuffer, bufferLength, 0 );

    /* The request document is a map with 1 key value pair. */
    cborRet = cbor_encoder_create_map( &encoder, &mapEncoder, 1 );

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &mapEncoder, "certificateSigningRequest" );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_string( &mapEncoder, pCsr, csrLength );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encoder_close_container( &encoder, &mapEncoder );
    }

    if( cborRet == CborNoError )
    {
        *pOutLengthWritten = cbor_encoder_get_buffer_size( &encoder, ( uint8_t * ) pBuffer );
    }
    else
    {
        LogError( ( "Error during CBOR encoding: %s", cbor_error_string( cborRet ) ) );

        if( ( cborRet & CborErrorOutOfMemory ) != 0 )
        {
            LogError( ( "Cannot fit CreateCertificateFromCsr request payload into buffer." ) );
        }
    }

    return( cborRet == CborNoError );
}
/*-----------------------------------------------------------*/

bool generateRegisterThingRequest( uint8_t * pBuffer,
                                   size_t bufferLength,
                                   const char * pCertificateOwnershipToken,
                                   size_t certificateOwnershipTokenLength,
                                   const char * pSerial,
                                   size_t serialLength,
                                   size_t * pOutLengthWritten )
{
    CborEncoder encoder, mapEncoder, parametersEncoder;
    CborError cborRet;

    assert( pBuffer != NULL );
    assert( pCertificateOwnershipToken != NULL );
    assert( pSerial != NULL );
    assert( pOutLengthWritten != NULL );

    /* For details on the RegisterThing request payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-request-payload
     */
    cbor_encoder_init( &encoder, pBuffer, bufferLength, 0 );
    /* The RegisterThing request payload is a map with two keys. */
    cborRet = cbor_encoder_create_map( &encoder, &mapEncoder, 2 );

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &mapEncoder, "certificateOwnershipToken" );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_string( &mapEncoder, pCertificateOwnershipToken, certificateOwnershipTokenLength );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &mapEncoder, "parameters" );
    }

    if( cborRet == CborNoError )
    {
        /* Parameters in this example is length 1. */
        cborRet = cbor_encoder_create_map( &mapEncoder, &parametersEncoder, 1 );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &parametersEncoder, "SerialNumber" );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_string( &parametersEncoder, pSerial, serialLength );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encoder_close_container( &mapEncoder, &parametersEncoder );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encoder_close_container( &encoder, &mapEncoder );
    }

    if( cborRet == CborNoError )
    {
        *pOutLengthWritten = cbor_encoder_get_buffer_size( &encoder, ( uint8_t * ) pBuffer );
    }
    else
    {
        LogError( ( "Error during CBOR encoding: %s", cbor_error_string( cborRet ) ) );

        if( ( cborRet & CborErrorOutOfMemory ) != 0 )
        {
            LogError( ( "Cannot fit RegisterThing request payload into buffer." ) );
        }
    }

    return( cborRet == CborNoError );
}
/*-----------------------------------------------------------*/

bool parseCsrResponse( const uint8_t * pResponse,
                       size_t length,
                       char * pCertificateBuffer,
                       size_t * pCertificateBufferLength,
                       char * pCertificateIdBuffer,
                       size_t * pCertificateIdBufferLength,
                       char * pOwnershipTokenBuffer,
                       size_t * pOwnershipTokenBufferLength )
{
    CborError cborRet;
    CborParser parser;
    CborValue map;
    CborValue value;

    assert( pResponse != NULL );
    assert( pCertificateBuffer != NULL );
    assert( pCertificateBufferLength != NULL );
    assert( pCertificateIdBuffer != NULL );
    assert( pCertificateIdBufferLength != NULL );
    assert( *pCertificateIdBufferLength >= 64 );
    assert( pOwnershipTokenBuffer != NULL );
    assert( pOwnershipTokenBufferLength != NULL );

    /* For details on the CreateCertificatefromCsr response payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-response-payload
     */
    cborRet = cbor_parser_init( pResponse, length, 0, &parser, &map );

    if( cborRet != CborNoError )
    {
        LogError( ( "Error initializing parser for CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
    }
    else if( !cbor_value_is_map( &map ) )
    {
        LogError( ( "CreateCertificateFromCsr response is not a valid map container type." ) );
    }
    else
    {
        cborRet = cbor_value_map_find_value( &map, "certificatePem", &value );

        if( cborRet != CborNoError )
        {
            LogError( ( "Error searching CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
        }
        else if( value.type == CborInvalidType )
        {
            LogError( ( "\"certificatePem\" not found in CreateCertificateFromCsr response." ) );
        }
        else if( value.type != CborTextStringType )
        {
            LogError( ( "Value for \"certificatePem\" key in CreateCertificateFromCsr response is not a text string type." ) );
        }
        else
        {
            cborRet = cbor_value_copy_text_string( &value, pCertificateBuffer, pCertificateBufferLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                size_t requiredLen = 0;
                ( void ) cbor_value_calculate_string_length( &value, &requiredLen );
                LogError( ( "Certificate buffer insufficiently large. Certificate length: %lu", ( unsigned long ) requiredLen ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Failed to parse \"certificatePem\" value from CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
            }
        }
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_value_map_find_value( &map, "certificateId", &value );

        if( cborRet != CborNoError )
        {
            LogError( ( "Error searching CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
        }
        else if( value.type == CborInvalidType )
        {
            LogError( ( "\"certificateId\" not found in CreateCertificateFromCsr response." ) );
        }
        else if( value.type != CborTextStringType )
        {
            LogError( ( "\"certificateId\" is an unexpected type in CreateCertificateFromCsr response." ) );
        }
        else
        {
            cborRet = cbor_value_copy_text_string( &value, pCertificateIdBuffer, pCertificateIdBufferLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                size_t requiredLen = 0;
                ( void ) cbor_value_calculate_string_length( &value, &requiredLen );
                LogError( ( "Certificate ID buffer insufficiently large. Certificate ID length: %lu", ( unsigned long ) requiredLen ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Failed to parse \"certificateId\" value from CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
            }
        }
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_value_map_find_value( &map, "certificateOwnershipToken", &value );

        if( cborRet != CborNoError )
        {
            LogError( ( "Error searching CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
        }
        else if( value.type == CborInvalidType )
        {
            LogError( ( "\"certificateOwnershipToken\" not found in CreateCertificateFromCsr response." ) );
        }
        else if( value.type != CborTextStringType )
        {
            LogError( ( "\"certificateOwnershipToken\" is an unexpected type in CreateCertificateFromCsr response." ) );
        }
        else
        {
            cborRet = cbor_value_copy_text_string( &value, pOwnershipTokenBuffer, pOwnershipTokenBufferLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                size_t requiredLen = 0;
                ( void ) cbor_value_calculate_string_length( &value, &requiredLen );
                LogError( ( "Certificate ownership token buffer insufficiently large. Certificate ownership token buffer length: %lu", ( unsigned long ) requiredLen ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Failed to parse \"certificateOwnershipToken\" value from CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
            }
        }
    }

    return( cborRet == CborNoError );
}
/*-----------------------------------------------------------*/

bool parseRegisterThingResponse( const uint8_t * pResponse,
                                 size_t length,
                                 char * pThingNameBuffer,
                                 size_t * pThingNameBufferLength )
{
    CborError cborRet;
    CborParser parser;
    CborValue map;
    CborValue value;

    assert( pResponse != NULL );
    assert( pThingNameBuffer != NULL );
    assert( pThingNameBufferLength != NULL );

    /* For details on the RegisterThing response payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-response-payload
     */
    cborRet = cbor_parser_init( pResponse, length, 0, &parser, &map );

    if( cborRet != CborNoError )
    {
        LogError( ( "Error initializing parser for RegisterThing response: %s.", cbor_error_string( cborRet ) ) );
    }
    else if( !cbor_value_is_map( &map ) )
    {
        LogError( ( "RegisterThing response not a map type." ) );
    }
    else
    {
        cborRet = cbor_value_map_find_value( &map, "thingName", &value );

        if( cborRet != CborNoError )
        {
            LogError( ( "Error searching RegisterThing response: %s.", cbor_error_string( cborRet ) ) );
        }
        else if( value.type == CborInvalidType )
        {
            LogError( ( "\"thingName\" not found in RegisterThing response." ) );
        }
        else if( value.type != CborTextStringType )
        {
            LogError( ( "\"thingName\" is an unexpected type in RegisterThing response." ) );
        }
        else
        {
            cborRet = cbor_value_copy_text_string( &value, pThingNameBuffer, pThingNameBufferLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                size_t requiredLen = 0;
                ( void ) cbor_value_calculate_string_length( &value, &requiredLen );
                LogError( ( "Thing name buffer insufficiently large. Thing name length: %lu", ( unsigned long ) requiredLen ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Failed to parse \"thingName\" value from RegisterThing response: %s.", cbor_error_string( cborRet ) ) );
            }
        }
    }

    return( cborRet == CborNoError );
}
/*-----------------------------------------------------------*/

static CborError cborPrinter( void * token,
                              const char * fmt,
                              ... )
{
    int result;
    va_list args;
    CborPrintContext_t * ctx = ( CborPrintContext_t * ) token;

    va_start( args, fmt );

    /* Compute length to write. */
    result = vsnprintf( NULL, 0, fmt, args );

    va_end( args );

    if( result < 0 )
    {
        LogError( ( "Error formatting CBOR string." ) );
    }
    else
    {
        size_t newLen = ( unsigned ) result;
        size_t oldLen = ctx->length;
        char * newPtr;

        ctx->length = oldLen + newLen;
        newPtr = ( char * ) realloc( ( void * ) ctx->str, ctx->length + 1 );

        if( newPtr == NULL )
        {
            LogError( ( "Failed to reallocate CBOR string." ) );
            result = -1;
        }
        else
        {
            va_start( args, fmt );

            result = vsnprintf( newPtr + oldLen, newLen + 1, fmt, args );

            va_end( args );

            ctx->str = newPtr;

            if( result < 0 )
            {
                LogError( ( "Error printing CBOR string." ) );
            }
        }
    }

    return ( result < 0 ) ? CborErrorIO : CborNoError;
}
/*-----------------------------------------------------------*/

const char * getStringFromCbor( const uint8_t * cbor,
                                size_t length )
{
    CborPrintContext_t printCtx = { 0 };
    CborParser parser;
    CborValue value;
    CborError error;

    error = cbor_parser_init( cbor, length, 0, &parser, &value );

    if( error == CborNoError )
    {
        error = cbor_value_to_pretty_stream( cborPrinter, &printCtx, &value, CborPrettyDefaultFlags );
    }

    if( error != CborNoError )
    {
        LogError( ( "Error printing CBOR payload." ) );
        printCtx.str = "";
    }

    return printCtx.str;
}
/*-----------------------------------------------------------*/
