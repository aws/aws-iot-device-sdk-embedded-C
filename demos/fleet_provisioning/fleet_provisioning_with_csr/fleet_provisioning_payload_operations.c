/*
 * AWS IoT Device SDK for Embedded C 202103.00
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

/* TinyCBOR library for CBOR encoding and decoding operations. */
#include "cbor.h"

/* Demo config. */
#include "demo_config.h"

/* AWS IoT Fleet Provisioning Library. */
#include "fleet_provisioning.h"

/* Header include. */
#include "fleet_provisioning_payload_operations.h"
/*-----------------------------------------------------------*/

bool generateCsrRequest( char * pBuffer,
                         size_t bufferLength,
                         const char * pCsr,
                         size_t csrLength,
                         size_t * pOutLengthWritten )
{
    bool status = false;
    CborEncoder encoder, mapEncoder;
    CborError cborRet;


    /* For details on the CreateCertificatefromCsr request payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#create-cert-csr-request-payload
     */
    if( status == true )
    {
        cbor_encoder_init( &encoder, ( uint8_t * ) pBuffer, bufferLength, 0 );

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
            status = false;
            LogError( ( "Error during CBOR encoding: %s", cbor_error_string( cborRet ) ) );

            if( ( cborRet & CborErrorOutOfMemory ) != 0 )
            {
                LogError( ( "Cannot fit CreateCertificateFromCsr request payload into buffer." ) );
            }
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

bool generateRegisterThingRequest( char * pBuffer,
                                   size_t bufferLength,
                                   const char * pCertificateOwnershipToken,
                                   size_t certificateOwnershipTokenLength,
                                   const char * pSerial,
                                   size_t serialLength,
                                   size_t * pOutLengthWritten )
{
    bool status = false;
    CborEncoder encoder, mapEncoder, parametersEncoder;
    CborError cborRet;

    /* For details on the RegisterThing request payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-request-payload
     */
    cbor_encoder_init( &encoder, ( uint8_t * ) pBuffer, bufferLength, 0 );
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
        status = true;
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

    return status;
}
/*-----------------------------------------------------------*/

bool parseCsrResponse( const char * pResponse,
                       size_t length,
                       char * pCertificate,
                       size_t * pCertificateLength,
                       char * pCertificateId,
                       size_t * pCertificateIdLength,
                       char * pOwnershipToken,
                       size_t * pOwnershipTokenLength )
{
    bool status = false;
    CborError cborRet;
    CborParser parser;
    CborValue map;
    CborValue value;

    /* For details on the CreateCertificatefromCsr response payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-response-payload
     */
    cborRet = cbor_parser_init( ( const uint8_t * ) pResponse, length, 0, &parser, &map );

    if( cborRet != CborNoError )
    {
        LogError( ( "Error initializing parser for CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
    }
    else if( !cbor_value_is_map( &map ) )
    {
        LogError( ( "CreateCertificateFromCsr response not a map type." ) );
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
            LogError( ( "\"certificatePem\" is an unexpected type in CreateCertificateFromCsr response." ) );
        }
        else
        {
            cborRet = cbor_value_copy_text_string( &value, pCertificate, pCertificateLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                LogError( ( "Certificate buffer insufficiently large." ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Error extracting \"certificatePem\" value from CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
            }
            else
            {
                status = true;
            }
        }
    }

    if( status == true )
    {
        status = false;
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
            cborRet = cbor_value_copy_text_string( &value, pCertificateId, pCertificateIdLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                LogError( ( "Certificate Id buffer insufficiently large." ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Error extracting \"certificateId\" value from CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
            }
            else
            {
                status = true;
            }
        }
    }

    if( status == true )
    {
        status = false;
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
            cborRet = cbor_value_copy_text_string( &value, pOwnershipToken, pOwnershipTokenLength, NULL );

            if( cborRet == CborErrorOutOfMemory )
            {
                LogError( ( "Certificate buffer insufficiently large." ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Error extracting \"certificateOwnershipToken\" value from CreateCertificateFromCsr response: %s.", cbor_error_string( cborRet ) ) );
            }
            else
            {
                status = true;
            }
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

bool parseRegisterThingResponse( const char * pResponse,
                                 size_t length,
                                 char * pThingNameBuffer,
                                 size_t * pThingNameBufferLength )
{
    bool status = true;
    CborError cborRet;
    CborParser parser;
    CborValue map;
    CborValue value;


    /* For details on the RegisterThing response payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-response-payload
     */
    cborRet = cbor_parser_init( ( const uint8_t * ) pResponse, length, 0, &parser, &map );

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
                LogError( ( "Thing name buffer insufficiently large." ) );
            }
            else if( cborRet != CborNoError )
            {
                LogError( ( "Error extracting \"thingName\" value from RegisterThing response: %s.", cbor_error_string( cborRet ) ) );
            }
            else
            {
                status = true;
            }
        }
    }

    return status;
}
/*-----------------------------------------------------------*/
