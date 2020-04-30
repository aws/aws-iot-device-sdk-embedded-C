/*
 * IoT Serializer V1.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* Unity framework includes. */
#include "unity_fixture.h"
#include "unity.h"

/* Serializer and CBOR includes. */
#include "iot_serializer.h"
#include "cbor.h"

#define BUFFER_SIZE    100

static const IotSerializerEncodeInterface_t * _pCborEncoder = NULL;
static const IotSerializerDecodeInterface_t * _pCborDecoder = NULL;

static IotSerializerEncoderObject_t _encoderObject;

static uint8_t _buffer[ BUFFER_SIZE ];

TEST_GROUP( Serializer_Unit_CBOR );

TEST_SETUP( Serializer_Unit_CBOR )
{
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    _pCborEncoder = IotSerializer_GetCborEncoder();
    _pCborDecoder = IotSerializer_GetCborDecoder();

    /* Reset buffer to zero. */
    memset( _buffer, 0, BUFFER_SIZE );

    /* Init encoder object with buffer. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->init( &_encoderObject, _buffer, BUFFER_SIZE ) );
}

TEST_TEAR_DOWN( Serializer_Unit_CBOR )
{
    /* Destroy encoder object. */
    _pCborEncoder->destroy( &_encoderObject );

    TEST_ASSERT_NULL( _encoderObject.pHandle );

    IotSdk_Cleanup();
}

/* TODO:
 * - append NULL
 * - append bool
 */
TEST_GROUP_RUNNER( Serializer_Unit_CBOR )
{
    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_init_with_null_buffer );

    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_append_integer );
    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_append_text_string );
    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_append_byte_string );

    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_open_a_scalar );
    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_open_map );
    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_open_array );

    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_map_nest_map );
    RUN_TEST_CASE( Serializer_Unit_CBOR, Encoder_map_nest_array );
}

TEST( Serializer_Unit_CBOR, Encoder_init_with_null_buffer )
{
    IotSerializerEncoderObject_t encoderObject = { .type = ( IotSerializerDataType_t ) 0 };

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->init( &encoderObject, NULL, 0 ) );

    /* Set the type to stream. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_CONTAINER_STREAM, encoderObject.type );

    /* Assigned value to handle pointer. */
    TEST_ASSERT_NOT_NULL( encoderObject.pHandle );

    /* Append an integer. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_BUFFER_TOO_SMALL, _pCborEncoder->append( &encoderObject,
                                                                               IotSerializer_ScalarSignedInt(
                                                                                   1 ) ) );

    /* Needed buffer size is 1 to encode integer "1". */
    TEST_ASSERT_EQUAL( 1, _pCborEncoder->getExtraBufferSizeNeeded( &encoderObject ) );

    _pCborEncoder->destroy( &encoderObject );

    TEST_ASSERT_NULL( encoderObject.pHandle );
}

TEST( Serializer_Unit_CBOR, Encoder_append_integer )
{
    int64_t value = 6;
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;
    scalarData.value.u.signedInt = value;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->append( &_encoderObject, scalarData ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermostValue;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermostValue ) );

    TEST_ASSERT_EQUAL( CborIntegerType, cbor_value_get_type( &outermostValue ) );

    int64_t result = 0;
    TEST_ASSERT_EQUAL( CborNoError, cbor_value_get_int64( &outermostValue, &result ) );

    TEST_ASSERT_EQUAL( value, result );

    /* Encoded size is 1. */
    TEST_ASSERT_EQUAL( 1, _pCborEncoder->getEncodedSize( &_encoderObject, _buffer ) );
}

TEST( Serializer_Unit_CBOR, Encoder_append_text_string )
{
    char * str = "hello world";
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
    scalarData.value.u.string.pString = ( uint8_t * ) str;
    scalarData.value.u.string.length = strlen( str );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->append( &_encoderObject, scalarData ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermostValue;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermostValue ) );

    TEST_ASSERT_EQUAL( CborTextStringType, cbor_value_get_type( &outermostValue ) );

    bool equal = false;
    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_text_string_equals( &outermostValue, str, &equal ) );

    TEST_ASSERT_TRUE( equal );
}

TEST( Serializer_Unit_CBOR, Encoder_append_byte_string )
{
    uint8_t inputBytes[] = "hello world";
    size_t inputLength = strlen( ( const char * ) inputBytes );
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_BYTE_STRING;
    scalarData.value.u.string.pString = ( uint8_t * ) inputBytes;
    scalarData.value.u.string.length = inputLength;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->append( &_encoderObject, scalarData ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermostValue;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermostValue ) );

    TEST_ASSERT_EQUAL( CborByteStringType, cbor_value_get_type( &outermostValue ) );

    uint8_t outputBytes[ 20 ];
    size_t outputLength = 20;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_copy_byte_string( &outermostValue, outputBytes, &outputLength,
                                                    NULL ) );

    TEST_ASSERT_EQUAL( inputLength, outputLength );

    TEST_ASSERT_EQUAL( 0, strcmp( ( const char * ) inputBytes, ( const char * ) outputBytes ) );
}

TEST( Serializer_Unit_CBOR, Encoder_open_a_scalar )
{
    IotSerializerEncoderObject_t integerObject =
    {
        .pHandle = NULL, .type = IOT_SERIALIZER_SCALAR_SIGNED_INT
    };

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_INVALID_INPUT,
                       _pCborEncoder->openContainer( &_encoderObject, &integerObject, 1 ) );
}

TEST( Serializer_Unit_CBOR, Encoder_open_map )
{
    IotSerializerEncoderObject_t mapObject = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
    scalarData.value.u.string.pString = ( uint8_t * ) "value";
    scalarData.value.u.string.length = 5;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->openContainer( &_encoderObject, &mapObject, 1 ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->appendKeyValue( &mapObject, "key", scalarData ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->closeContainer( &_encoderObject, &mapObject ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermostValue, value;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermostValue ) );

    TEST_ASSERT_EQUAL( CborMapType, cbor_value_get_type( &outermostValue ) );

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_map_find_value( &outermostValue, "key", &value ) );

    TEST_ASSERT_EQUAL( CborTextStringType, cbor_value_get_type( &value ) );

    bool equal = false;
    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_text_string_equals( &value, "value", &equal ) );

    TEST_ASSERT_TRUE( equal );
}

TEST( Serializer_Unit_CBOR, Encoder_open_array )
{
    uint8_t i = 0;
    IotSerializerEncoderObject_t arrayObject = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_ARRAY;

    int64_t numberArray[] = { 3, 2, 1 };
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->openContainer( &_encoderObject, &arrayObject, 3 ) );

    for( i = 0; i < 3; i++ )
    {
        scalarData.value.u.signedInt = numberArray[ i ];

        TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                           _pCborEncoder->append( &arrayObject, scalarData ) );
    }

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->closeContainer( &_encoderObject, &arrayObject ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermostValue, arrayValue;
    int64_t number = 0;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermostValue ) );

    TEST_ASSERT_EQUAL( CborArrayType, cbor_value_get_type( &outermostValue ) );

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_enter_container( &outermostValue, &arrayValue ) );

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( CborIntegerType, cbor_value_get_type( &arrayValue ) );
        TEST_ASSERT_EQUAL( CborNoError, cbor_value_get_int64( &arrayValue, &number ) );
        TEST_ASSERT_EQUAL( numberArray[ i ], number );

        TEST_ASSERT_EQUAL( CborNoError, cbor_value_advance( &arrayValue ) );
    }

    TEST_ASSERT_TRUE( cbor_value_at_end( &arrayValue ) );
}

TEST( Serializer_Unit_CBOR, Encoder_map_nest_map )
{
    IotSerializerEncoderObject_t mapObject_1 = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerEncoderObject_t mapObject_2 = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_TEXT_STRING;
    scalarData.value.u.string.pString = ( uint8_t * ) "value";
    scalarData.value.u.string.length = 5;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->openContainer( &_encoderObject, &mapObject_1, 1 ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->openContainerWithKey( &mapObject_1, "map1", &mapObject_2,
                                                            1 ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->appendKeyValue( &mapObject_2, "key", scalarData ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->closeContainer( &mapObject_1, &mapObject_2 ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->closeContainer( &_encoderObject, &mapObject_1 ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermostValue, map1, str;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermostValue ) );

    TEST_ASSERT_EQUAL( CborMapType, cbor_value_get_type( &outermostValue ) );

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_map_find_value( &outermostValue, "map1", &map1 ) );

    TEST_ASSERT_EQUAL( CborMapType, cbor_value_get_type( &map1 ) );

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_map_find_value( &map1, "key", &str ) );

    TEST_ASSERT_EQUAL( CborTextStringType, cbor_value_get_type( &str ) );

    bool equal = false;
    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_text_string_equals( &str, "value", &equal ) );

    TEST_ASSERT_TRUE( equal );
}

TEST( Serializer_Unit_CBOR, Encoder_map_nest_array )
{
    uint8_t i = 0;
    IotSerializerEncoderObject_t mapObject = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerEncoderObject_t arrayObject = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_ARRAY;
    IotSerializerScalarData_t scalarData = { 0 };

    scalarData.type = IOT_SERIALIZER_SCALAR_SIGNED_INT;

    int64_t numberArray[] = { 3, 2, 1 };

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->openContainer( &_encoderObject, &mapObject, 1 ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->openContainerWithKey( &mapObject, "array", &arrayObject,
                                                            3 ) );

    for( i = 0; i < 3; i++ )
    {
        scalarData.value.u.signedInt = numberArray[ i ];

        TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                           _pCborEncoder->append( &arrayObject, scalarData ) );
    }

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->closeContainer( &mapObject, &arrayObject ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborEncoder->closeContainer( &_encoderObject, &mapObject ) );

    /* --- Verification --- */

    CborParser parser;
    CborValue outermost, array, arrayElement;
    int64_t number = 0;

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_parser_init( _buffer, BUFFER_SIZE, 0, &parser, &outermost ) );

    TEST_ASSERT_EQUAL( CborMapType, cbor_value_get_type( &outermost ) );

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_map_find_value( &outermost, "array", &array ) );

    TEST_ASSERT_EQUAL( CborArrayType, cbor_value_get_type( &array ) );

    TEST_ASSERT_EQUAL( CborNoError,
                       cbor_value_enter_container( &array, &arrayElement ) );

    for( i = 0; i < 3; i++ )
    {
        TEST_ASSERT_EQUAL( CborIntegerType, cbor_value_get_type( &arrayElement ) );
        TEST_ASSERT_EQUAL( CborNoError, cbor_value_get_int64( &arrayElement, &number ) );
        TEST_ASSERT_EQUAL( numberArray[ i ], number );

        TEST_ASSERT_EQUAL( CborNoError, cbor_value_advance( &arrayElement ) );
    }

    TEST_ASSERT_TRUE( cbor_value_at_end( &arrayElement ) );
}

static const uint8_t _testEncodedNestedMap[] =
{
    0xA2, /* # map(2) */
    0x61, /* # text(1) */
    0x31, /* # "1" */
    0xA1, /* # map(1) */
    0x61, /* # text(1) */
    0x41, /* # "A" */
    0x0A, /* # unsigned(10) */
    0x61, /* # text(1) */
    0x33, /* # "3" */
    0xF4, /* # false */
};

TEST_GROUP( Serializer_Decoder_Unit_CBOR );

TEST_SETUP( Serializer_Decoder_Unit_CBOR )
{
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    _pCborDecoder = IotSerializer_GetCborDecoder();
}

TEST_TEAR_DOWN( Serializer_Decoder_Unit_CBOR )
{
    IotSdk_Cleanup();
}

TEST_GROUP_RUNNER( Serializer_Decoder_Unit_CBOR )
{
    RUN_TEST_CASE( Serializer_Decoder_Unit_CBOR, TestDecoderObjectWithNestedMap );
    RUN_TEST_CASE( Serializer_Decoder_Unit_CBOR, TestDecoderIteratorWithNestedMap );
    RUN_TEST_CASE( Serializer_Decoder_Unit_CBOR, TestGetSizeOfForIndefiniteLengthMap );
    RUN_TEST_CASE( Serializer_Decoder_Unit_CBOR, TestGetSizeOfForIndefiniteLengthArray );
    RUN_TEST_CASE( Serializer_Decoder_Unit_CBOR, TestDecoderObjectReuseAfterIteration );
}

TEST( Serializer_Decoder_Unit_CBOR, TestDecoderObjectWithNestedMap )
{
    IotSerializerDecoderObject_t outermostDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    size_t numOfEntriesInOuterMap;
    const uint8_t * pDecoderObjectStartAddr = NULL;
    size_t decoderDataLength = 0;
    IotSerializerDecoderObject_t outerMapDecoder1 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t innerMapDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    size_t numOfEntriesInInnerMap;
    IotSerializerDecoderObject_t outerMapDecoder2 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    size_t unsupportedTypeDecoderObjectLength = 0;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->init( &outermostDecoder,
                                                                    _testEncodedNestedMap,
                                                                    sizeof( _testEncodedNestedMap ) ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_CONTAINER_MAP, outermostDecoder.type );


    /* Verify the functionality of getSizeOf() API on the outer map. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getSizeOf( &outermostDecoder, &numOfEntriesInOuterMap ) );
    TEST_ASSERT_EQUAL( 2, numOfEntriesInOuterMap );

    /* Make sure that the getBufferAddress() API returns the first location of the buffer for the
     * outermost decoder object.*/
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborDecoder->getBufferAddress( &outermostDecoder,
                                                        &pDecoderObjectStartAddr ) );
    TEST_ASSERT_EQUAL_PTR( &_testEncodedNestedMap[ 0 ], pDecoderObjectStartAddr );

    /* Verify that the getSizeOfEncodedData() correctly calculates the length of the outermost decoder
     * data. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getSizeOfEncodedData(
                           &outermostDecoder, &decoderDataLength ) );
    TEST_ASSERT_EQUAL( sizeof( _testEncodedNestedMap ), decoderDataLength );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->find( &outermostDecoder, "1",
                                                                    &outerMapDecoder1 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_CONTAINER_MAP, outerMapDecoder1.type );

    /* Verify the functionality of getSizeOf() API on the inner map. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getSizeOf( &outerMapDecoder1, &numOfEntriesInInnerMap ) );
    TEST_ASSERT_EQUAL( 1, numOfEntriesInInnerMap );

    /* Make sure that the getBufferAddress() API returns the first location in the buffer to the value
     * for the entry keyed by "1".*/
    TEST_ASSERT_EQUAL_PTR( IOT_SERIALIZER_SUCCESS,
                           _pCborDecoder->getBufferAddress( &outerMapDecoder1,
                                                            &pDecoderObjectStartAddr ) );
    TEST_ASSERT_EQUAL_PTR( &_testEncodedNestedMap[ 3 ], pDecoderObjectStartAddr );

    /* Verify that the getSizeOfEncodedData() correctly calculates the length of the container type
     * value of the entry keyed by "1" */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getSizeOfEncodedData(
                           &outerMapDecoder1, &decoderDataLength ) );
    TEST_ASSERT_EQUAL( 4u, decoderDataLength );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->find( &outerMapDecoder1, "A",
                                                                    &innerMapDecoder ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SCALAR_SIGNED_INT, innerMapDecoder.type );

    /* Make sure that the getBufferAddress() API does not support getting buffer address of value in the
     * the nested entry keyed by "A".*/
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_NOT_SUPPORTED,
                       _pCborDecoder->getBufferAddress( &innerMapDecoder,
                                                        &pDecoderObjectStartAddr ) );

    /* Verify that the getSizeOfEncodedData() does not support calculation of non-container type data.*/
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_NOT_SUPPORTED,
                       _pCborDecoder->getSizeOfEncodedData(
                           &innerMapDecoder, &unsupportedTypeDecoderObjectLength ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->find( &outermostDecoder, "3",
                                                                    &outerMapDecoder2 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SCALAR_BOOL, outerMapDecoder2.type );

    /* Make sure that the getBufferAddress() API does not give the buffer address of the value data
     * in the entry keyed by "3".*/
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_NOT_SUPPORTED,
                       _pCborDecoder->getBufferAddress( &outerMapDecoder2,
                                                        &pDecoderObjectStartAddr ) );

    /* Verify that the getSizeOfEncodedData() does not support calculation of non-container type data.*/
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_NOT_SUPPORTED,
                       _pCborDecoder->getSizeOfEncodedData(
                           &outerMapDecoder2, &unsupportedTypeDecoderObjectLength ) );

    _pCborDecoder->destroy( &outerMapDecoder1 );
    _pCborDecoder->destroy( &outerMapDecoder2 );
    _pCborDecoder->destroy( &outermostDecoder );
}

TEST( Serializer_Decoder_Unit_CBOR, TestDecoderIteratorWithNestedMap )
{
    IotSerializerDecoderObject_t outerDecoder1 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderIterator_t outerIter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    const uint8_t * pDecoderObjectStartAddr = NULL;
    IotSerializerDecoderObject_t iterToDecoderObject = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t iterToDecoderObject2 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t iterToDecoderObject3 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t outerDecoder2 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t nestedMapDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderIterator_t nestedMapIter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->init( &outerDecoder1,
                                                                    _testEncodedNestedMap,
                                                                    sizeof( _testEncodedNestedMap ) ) );

    /* Obtain an iterator to the contents of the map. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &outerDecoder1,
                                                                      &outerIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( outerIter,
                                                                   &iterToDecoderObject ) );
    /* Validate that we can obtain the key data of the first entry in the outer map. */
    TEST_ASSERT_EQUAL_STRING_LEN( "1", iterToDecoderObject.u.value.u.string.pString,
                                  iterToDecoderObject.u.value.u.string.length );


    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( outerIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( outerIter,
                                                                   &iterToDecoderObject ) );
    /* Validate that we can obtain the value data (i.e. nested map) of the first entry in the parent/outer map. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getBufferAddress(
                           &iterToDecoderObject, &pDecoderObjectStartAddr ) );
    TEST_ASSERT_EQUAL_PTR( &_testEncodedNestedMap[ 3 ], pDecoderObjectStartAddr );
    _pCborDecoder->destroy( &iterToDecoderObject );


    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( outerIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( outerIter,
                                                                   &iterToDecoderObject2 ) );
    /* Validate that we can obtain the key data of the second entry in the outer map. */
    TEST_ASSERT_EQUAL_STRING_LEN( "3", iterToDecoderObject2.u.value.u.string.pString,
                                  iterToDecoderObject2.u.value.u.string.length );
    _pCborDecoder->destroy( &iterToDecoderObject2 );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( outerIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( outerIter,
                                                                   &iterToDecoderObject2 ) );
    /* Validate that we can obtain the boolean value data of the second entry in the outer map. */
    TEST_ASSERT_EQUAL( false, iterToDecoderObject2.u.value.u.booleanValue );
    _pCborDecoder->destroy( &iterToDecoderObject2 );

    /* Iterate to the end of the outer map container. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( outerIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( outerIter,
                                                                       &outerDecoder1 ) );
    _pCborDecoder->destroy( &outerDecoder1 );


    /* Test with iterating in the nested map in the entry keyed by "1" */

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->init( &outerDecoder2,
                                                                    _testEncodedNestedMap,
                                                                    sizeof( _testEncodedNestedMap ) ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->find( &outerDecoder2, "1",
                                                                    &nestedMapDecoder ) );

    /* Obtain an iterator to the contents of the nested map. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &nestedMapDecoder,
                                                                      &nestedMapIter ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( nestedMapIter,
                                                                   &iterToDecoderObject3 ) );
    /* Validate that we can obtain the key data of the only entry in the nested map. */
    TEST_ASSERT_EQUAL_STRING_LEN( "A", iterToDecoderObject3.u.value.u.string.pString,
                                  iterToDecoderObject3.u.value.u.string.length );


    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( nestedMapIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( nestedMapIter,
                                                                   &iterToDecoderObject3 ) );
    /* Validate that we can obtain the integer value of the only entry in the nested map. */
    TEST_ASSERT_EQUAL_INT( 10, iterToDecoderObject3.u.value.u.signedInt );

    /* Iterate to the end of the nested map container. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( nestedMapIter ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( nestedMapIter,
                                                                       &nestedMapDecoder ) );
    _pCborDecoder->destroy( &nestedMapDecoder );
    _pCborDecoder->destroy( &outerDecoder2 );
}

TEST( Serializer_Decoder_Unit_CBOR, TestGetSizeOfForIndefiniteLengthMap )
{
    const uint8_t pSampleIndefiniteLengthMap[] =
    {
        0xBF,                   /*# map(*)  <---------------   Indefinite map length */
        0x64,                   /*# text(4) */
        0x4B, 0x65, 0x79, 0x31, /*# "Key1" */
        0x01,                   /*# unsigned(1) */
        0x64,                   /*# text(4) */
        0x4B, 0x65, 0x79, 0x32, /*# "Key2" */
        0x64,                   /*# text(4) */
        0x4C, 0x61, 0x73, 0x74, /*# "Last" */
        0xFF,                   /*# primitive(*) <------------------ "break" */
    };

    IotSerializerDecoderObject_t mapDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    size_t mapSize = 0;
    IotSerializerDecoderIterator_t iter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    IotSerializerDecoderObject_t keyObject = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t valueObject = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t valueObject2 = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS,
                       _pCborDecoder->init( &mapDecoder,
                                            pSampleIndefiniteLengthMap,
                                            sizeof( pSampleIndefiniteLengthMap ) ) );

    /* Test that size of an indefinite length map can be calculated. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getSizeOf( &mapDecoder, &mapSize ) );
    TEST_ASSERT_EQUAL( 2, mapSize );

    /* Test iterating through the map and extracting the first and last elements. */

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &mapDecoder, &iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( iter, &keyObject ) );

    /* Validate that we can obtain the first key value in the indefinite length map. */
    TEST_ASSERT_EQUAL_STRING_LEN( "Key1", keyObject.u.value.u.string.pString,
                                  keyObject.u.value.u.string.length );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );

    /* The last element is a special case for byte/text string extraction due to the succeeding byte being the "break"
     * byte. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( iter, &valueObject ) );
    TEST_ASSERT_EQUAL_STRING_LEN( "Last", valueObject.u.value.u.string.pString,
                                  valueObject.u.value.u.string.length );


    /* Make sure that we can obtain the same value entry from the "find()" API */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->find( &mapDecoder, "Key2", &valueObject2 ) );
    TEST_ASSERT_EQUAL_STRING_LEN( "Last", valueObject2.u.value.u.string.pString,
                                  valueObject2.u.value.u.string.length );

    /* Destroy the iterator. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( iter, &mapDecoder ) );

    _pCborDecoder->destroy( &keyObject );
    _pCborDecoder->destroy( &valueObject );
    _pCborDecoder->destroy( &mapDecoder );
}

TEST( Serializer_Decoder_Unit_CBOR, TestGetSizeOfForIndefiniteLengthArray )
{
    const uint8_t pSampleIndefiniteLengthMap[] =
    {
        0x9F,                   /*# array(*)  <---------------   Indefinite length array */
        0x63,                   /*# text(3) */
        0x45, 0x6C, 0x31,       /*# "El1" */
        0x01,                   /*# unsigned(1) */
        0x63,                   /*# text(3) */
        0x45, 0x6C, 0x33,       /*# "El3" */
        0x9F,                   /*# array(*)  <---------------   Indefinite length nested array */
        0x64,                   /*# text(4) */
        0x4C, 0x61, 0x73, 0x74, /*# "Last" */
        0xFF,                   /*# primitive(*) <------------------ "break" */
        0xFF,                   /*# primitive(*) <------------------ "break" */
    };

    IotSerializerDecoderObject_t arrayDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    size_t arraySize = 0;
    IotSerializerDecoderIterator_t iter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    IotSerializerDecoderIterator_t nestedIter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    IotSerializerDecoderObject_t elementObject = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t nestedArrayObject = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t nestedObject = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;


    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->init( &arrayDecoder,
                                                                    pSampleIndefiniteLengthMap,
                                                                    sizeof( pSampleIndefiniteLengthMap ) ) );

    /* Test that size of an indefinite length map can be calculated. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->getSizeOf( &arrayDecoder, &arraySize ) );
    TEST_ASSERT_EQUAL( 4, arraySize );

    /* Test iterating through the array and extracting the first and last elements. */

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &arrayDecoder, &iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( iter, &elementObject ) );

    /* Validate that we can obtain the first element value in the indefinite length array. */
    TEST_ASSERT_EQUAL_STRING_LEN( "El1", elementObject.u.value.u.string.pString,
                                  elementObject.u.value.u.string.length );

    /* Go to the last element in the list. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );

    /* The last element is a special case for byte/text string extraction as it is an indefinite-length nested array
     * within the outer indefinite-length array. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( iter, &nestedArrayObject ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &nestedArrayObject, &nestedIter ) );

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->get( nestedIter, &nestedObject ) );
    TEST_ASSERT_EQUAL_STRING_LEN( "Last", nestedObject.u.value.u.string.pString,
                                  nestedObject.u.value.u.string.length );

    /* Destroy the iterators. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( nestedIter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( nestedIter, &nestedArrayObject ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iter ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( iter, &arrayDecoder ) );

    _pCborDecoder->destroy( &nestedObject );
    _pCborDecoder->destroy( &nestedArrayObject );
    _pCborDecoder->destroy( &elementObject );
    _pCborDecoder->destroy( &arrayDecoder );
}

/* Verifies that a container decoder object remains valid for re-use after a complete round of iterating
 * through its contents */
TEST( Serializer_Decoder_Unit_CBOR, TestDecoderObjectReuseAfterIteration )
{
    IotSerializerDecoderObject_t mapDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderIterator_t iterator1 = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    IotSerializerDecoderObject_t valueDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderIterator_t iterator2 = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;

    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->init( &mapDecoder,
                                                                    _testEncodedNestedMap,
                                                                    sizeof( _testEncodedNestedMap ) ) );

    /* Obtain an iterator to the contents of the map. */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &mapDecoder,
                                                                      &iterator1 ) );


    /* Undergo one round of iteration through the map */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator1 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator1 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator1 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator1 ) );

    /* End the iteration by invalidating the iterator */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( iterator1, &mapDecoder ) );

    /* NOW check that the decoder object of the map is still valid! */
    /* Sanity check with "find()" function". */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->find( &mapDecoder, "3", &valueDecoder ) );
    TEST_ASSERT_EQUAL( false, valueDecoder.u.value.u.booleanValue );

    /* Sanity check with another round of iteration! */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepIn( &mapDecoder,
                                                                      &iterator2 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator2 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator2 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator2 ) );
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->next( iterator2 ) );

    /* End the second round of iteration */
    TEST_ASSERT_EQUAL( IOT_SERIALIZER_SUCCESS, _pCborDecoder->stepOut( iterator2, &mapDecoder ) );

    _pCborDecoder->destroy( &valueDecoder );
    _pCborDecoder->destroy( &mapDecoder );
}
