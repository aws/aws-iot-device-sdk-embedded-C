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

/*
 * Demo for showing use of the Fleet Provisioning library to use the Fleet
 * Provisioning feature of AWS IoT Core for provisioning devices with
 * credentials. This demo shows how a device can be provisioned with AWS IoT
 * Core using the Certificate Signing Request workflow of the Fleet
 * Provisioning feature.
 *
 * The Fleet Provisioning library provides macros and helper functions for
 * assembling MQTT topics strings, and for determining whether an incoming MQTT
 * message is related to the Fleet Provisioning API of AWS IoT Core. The Fleet
 * Provisioning library does not depend on any particular MQTT library,
 * therefore the functionality for MQTT operations is placed in another file
 * (mqtt_operations.c). This demo uses the coreMQTT library. If needed,
 * mqtt_operations.c can be modified to replace coreMQTT with another MQTT
 * library. This demo requires using the AWS IoT Core broker as Fleet
 * Provisioning is an AWS IoT Core feature.
 *
 * This demo provisions a device certificate using the provisioning by claim
 * workflow with a Certificate Signing Request (CSR). The demo connects to AWS
 * IoT Core using provided claim credentials (whose certificate needs to be
 * registered with IoT Core before running this demo), subscribes to the
 * CreateCertificateFromCsr topics, and obtains a certificate. It then
 * subscribes to the RegisterThing topics and activates the certificate and
 * obtains a Thing using the provisioning template. Finally, it reconnects to
 * AWS IoT Core using the new credentials.
 */

/* Standard includes. */
#include <stdlib.h>

/* POSIX includes. */
#include <unistd.h>
#include <errno.h>

/* Demo config. */
#include "demo_config.h"

/* MQTT operations. */
#include "mqtt_operations.h"

/* TinyCBOR library for CBOR encoding and decoding operations. */
#include "cbor.h"

/* AWS IoT Fleet Provisioning Library. */
#include "fleet_provisioning.h"

/**
 * These configurations are required. Throw compilation error if it is not
 * defined.
 */
#ifndef PROVISIONING_TEMPLATE_NAME
    #error "Please define PROVISIONING_TEMPLATE_NAME to the template name registered with AWS IoT Core in demo_config.h."
#endif
#ifndef CLAIM_CERT_PATH
    #error "Please define path to claim certificate (CLAIM_CERT_PATH) in demo_config.h."
#endif
#ifndef CLAIM_PRIVATE_KEY_PATH
    #error "Please define path to claim private key (CLAIM_PRIVATE_KEY_PATH) in demo_config.h."
#endif
#ifndef PROVISIONING_PRIVATE_KEY_PATH
    #error "Please define path to private key to provision (PROVISIONING_PRIVATE_KEY_PATH) in demo_config.h."
#endif
#ifndef PROVISIONING_CSR_PATH
    #error "Please define path to CSR to use to provision (PROVISIONING_CSR_PATH) in demo_config.h."
#endif
#ifndef PROVISIONING_CERT_PATH
    #error "Please define path to which to write the obtained certificate (PROVISIONING_CERT_PATH) in demo_config.h."
#endif

/**
 * @brief The length of #PROVISIONING_TEMPLATE_NAME.
 */
#define PROVISIONING_TEMPLATE_NAME_LENGTH    ( ( uint16_t ) ( sizeof( PROVISIONING_TEMPLATE_NAME ) - 1 ) )

/**
 * @brief Size of AWS IoT Thing name buffer.
 *
 * See https://docs.aws.amazon.com/iot/latest/apireference/API_CreateThing.html#iot-CreateThing-request-thingName
 */
#define MAX_THING_NAME_LENGTH                128

/**
 * @brief Number of seconds to wait for response from AWS IoT Fleet
 * Provisioning APIs.
 */
#define FLEET_PROV_RESPONSE_WAIT_SECONDS     ( 2 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef FLEET_PROV_MAX_DEMO_LOOP_COUNT
    #define FLEET_PROV_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in seconds to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_SECONDS    ( 5 )

/**
 * @brief Size of buffer in which to hold the certificate.
 */
#define CERT_BUFFER_LENGTH                             2048

/**
 * @brief Size of buffer in which to hold the certificate id.
 *
 * See https://docs.aws.amazon.com/iot/latest/apireference/API_Certificate.html#iot-Type-Certificate-certificateId
 */
#define CERT_ID_BUFFER_LENGTH                          64

/**
 * @brief Size of buffer in which to hold the certificate ownership token.
 */
#define OWNERSHIP_TOKEN_BUFFER_LENGTH                  512

/**
 * @brief Status values of the Fleet Provisioning response.
 */
typedef enum
{
    ResponseNotReceived,
    ResponseAccepted,
    ResponseRejected
} ResponseStatus_t;

/*-----------------------------------------------------------*/

/**
 * @brief Status reported from the MQTT publish callback.
 */
static ResponseStatus_t responseStatus;

/**
 * @brief Buffer to hold the provisioned AWS IoT Thing name.
 */
static char thingName[ MAX_THING_NAME_LENGTH ];

/**
 * @brief Length of the AWS IoT Thing name.
 */
static size_t thingNameLength;

/**
 * @brief Buffer to hold responses received from the AWS IoT Fleet Provisioning APIs.
 */
static char payloadBuffer[ NETWORK_BUFFER_SIZE ];

/**
 * @brief Length of the payload stored in #payloadBuffer.
 */
static size_t payloadLength;

/*-----------------------------------------------------------*/

/**
 * @brief Callback to receive the incoming publish messages from the MQTT
 * broker. Sets responseStatus if an expected CreateCertificateFromCsr or
 * RegisterThing response is received, and copies the response into
 * responseBuffer if the response is an accepted one.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] packetIdentifier Packet identifier of the incoming publish.
 */
static void provisioningPublishCallback( MQTTPublishInfo_t * pPublishInfo,
                                         uint16_t packetIdentifier );

/**
 * @brief Obtains the CSR from the file path in #PROVISIONING_CSR_PATH.
 *
 * @param[in] buffer Buffer into which to read the CSR.
 * @param[in] bufferLength Length of #buffer.
 * @param[out] outCsrLength The length of the CSR.
 */
static bool getCsr( char * buffer,
                    size_t bufferLength,
                    size_t * outCsrLength );

/**
 * @brief Creates the document to be published to the CreateCertificateFromCsr
 * API in order to provision a certificate with the included CSR.
 *
 * @param[in] buffer Buffer into which to write the publish document.
 * @param[in] bufferLength Length of #buffer.
 * @param[out] outLengthWritten The length of the publish document.
 */
static bool generateCsrRequest( char * buffer,
                                size_t bufferLength,
                                size_t * outLengthWritten );

/**
 * @brief Creates the document to be published to the RegisterThing API in order
 * to activate the provisioned certificate and receive a Thing name.
 *
 * @param[in] buffer Buffer into which to write the publish document.
 * @param[in] bufferLength Length of #buffer.
 * @param[in] certificateOwnershipToken The certificate's certificate ownership
 * token.
 * @param[in] certificateOwnershipTokenLength Length of #certificateOwnershipToken.
 * @param[out] outLengthWritten The length of the publish document.
 */
static bool generateRegisterThingRequest( char * buffer,
                                          size_t bufferLength,
                                          const char * certificateOwnershipToken,
                                          size_t certificateOwnershipTokenLength,
                                          const char * serial,
                                          size_t serialLength,
                                          size_t * outLengthWritten );

/**
 * @brief Extracts the certificate, certificate ID, and certificate ownership
 * token from a CreateCertificateFromCsr accepted response.
 *
 * @param[in] response The response document.
 * @param[in] length Length of #response.
 * @param[in] certificate The buffer to which to write the certificate.
 * @param[in,out] certificateLength The length of #certificate. The written
 * length is output here.
 * @param[in] certificateId The buffer to which to write the certificate ID.
 * @param[in,out] certificateIdLength The length of #certificateId. The written
 * length is output here.
 * @param[in] ownershipToken The buffer to which to write the certificate
 * ownership token.
 * @param[in,out] ownershipTokenLength The length of #ownershipToken. The written
 * length is output here.
 */
static bool parseCsrResponse( const char * response,
                              size_t length,
                              char * certificate,
                              size_t * certificateLength,
                              char * certificateId,
                              size_t * certificateIdLength,
                              char * ownershipToken,
                              size_t * ownershipTokenLength );

/**
 * @brief Extracts the Thing name from a RegisterThing accepted response.
 *
 * @param[in] response The response document.
 * @param[in] length Length of #response.
 * @param[in] thingNameBuffer The buffer to which to write the Thing name.
 * @param[in,out] thingNameBufferLength The length of #thingNameBuffer. The written
 * length is output here.
 */
static bool parseRegisterThingResponse( const char * response,
                                        size_t length,
                                        char * thingNameBuffer,
                                        size_t * thingNameBufferLength );

/**
 * @brief Run the MQTT process loop to get a response.
 */
static bool waitForResponse( void );

/**
 * @brief Subscribe to the CreateCertificateFromCsr accepted and rejected topics.
 */
static bool subscribeToCsrResponseTopics( void );

/**
 * @brief Unsubscribe from the CreateCertificateFromCsr accepted and rejected topics.
 */
static bool unsubscribeFromCsrResponseTopics( void );

/**
 * @brief Subscribe to the RegisterThing accepted and rejected topics.
 */
static bool subscribeToRegisterThingResponseTopics( void );

/**
 * @brief Unsubscribe from the RegisterThing accepted and rejected topics.
 */
static bool unsubscribeFromRegisterThingResponseTopics( void );

/**
 * @brief Save the certificate to the path specified by #PROVISIONING_CERT_PATH.
 */
static bool saveCertificate( const char * certificate,
                             size_t certificateLength );
/*-----------------------------------------------------------*/

static void provisioningPublishCallback( MQTTPublishInfo_t * pPublishInfo,
                                         uint16_t packetIdentifier )
{
    FleetProvisioningStatus_t status;
    FleetProvisioningTopic_t api;

    /* Silence compiler warnings about unused variables. */
    ( void ) packetIdentifier;

    status = FleetProvisioning_MatchTopic( pPublishInfo->pTopicName,
                                           pPublishInfo->topicNameLength, &api );

    if( status != FleetProvisioningSuccess )
    {
        LogError( ( "Unexpected publish message received. Topic: %.*s.",
                    ( int ) pPublishInfo->topicNameLength,
                    ( const char * ) pPublishInfo->pTopicName ) );
    }
    else
    {
        if( api == FleetProvCborCreateCertFromCsrAccepted )
        {
            LogInfo( ( "Fleet Provisioning CreateCertificateFromCsr accepted." ) );

            responseStatus = ResponseAccepted;

            ( void ) memcpy( ( void * ) payloadBuffer,
                             ( const void * ) pPublishInfo->pPayload,
                             ( size_t ) pPublishInfo->payloadLength );

            payloadLength = pPublishInfo->payloadLength;
        }
        else if( api == FleetProvCborCreateCertFromCsrRejected )
        {
            LogError( ( "Fleet Provisioning CreateCertificateFromCsr rejected." ) );

            responseStatus = ResponseRejected;
        }
        else if( api == FleetProvCborRegisterThingAccepted )
        {
            LogInfo( ( "Fleet Provisioning RegisterThing accepted." ) );

            responseStatus = ResponseAccepted;

            ( void ) memcpy( ( void * ) payloadBuffer,
                             ( const void * ) pPublishInfo->pPayload,
                             ( size_t ) pPublishInfo->payloadLength );

            payloadLength = pPublishInfo->payloadLength;
        }
        else if( api == FleetProvCborCreateCertFromCsrRejected )
        {
            LogError( ( "Fleet Provisioning RegisterThing rejected." ) );

            responseStatus = ResponseRejected;
        }
        else
        {
            LogError( ( "Unexpected Fleet Provisioning message. Topic: %.*s.",
                        ( int ) pPublishInfo->topicNameLength,
                        ( const char * ) pPublishInfo->pTopicName ) );
        }
    }
}
/*-----------------------------------------------------------*/

static bool getCsr( char * buffer,
                    size_t bufferLength,
                    size_t * outCsrLength )
{
    FILE * file;
    size_t length = 0;
    bool status = true;

    /* Get the file descriptor for the CSR file. */
    file = fopen( PROVISIONING_CSR_PATH, "rb" );

    if( file == NULL )
    {
        LogError( ( "Error opening file at PROVISIONING_CSR_PATH: %s. Error: %s.",
                    PROVISIONING_CSR_PATH, strerror( errno ) ) );
        status = false;
    }
    else
    {
        int result;
        /* Seek to the end of the file, so that we can get the file size. */
        result = fseek( file, 0L, SEEK_END );

        if( result == -1 )
        {
            LogError( ( "Failed while moving to end of the certificate signing request file. Path: %s. Error: %s.",
                        PROVISIONING_CSR_PATH, strerror( errno ) ) );
            status = false;
        }
        else
        {
            long lenResult = -1;
            /* Get the current position which is the file size. */
            lenResult = ftell( file );

            if( lenResult == -1 )
            {
                LogError( ( "Failed to get length of certificate signing request file. Path: %s. Error: %s.",
                            PROVISIONING_CSR_PATH, strerror( errno ) ) );
                status = false;
            }
            else
            {
                length = ( size_t ) lenResult;
            }
        }

        if( status == true )
        {
            if( length > bufferLength )
            {
                LogError( ( "Buffer too small for certificate signing request. Buffer size: %ld. Required size: %ld.",
                            bufferLength, length ) );
                status = false;
            }
        }

        if( status == true )
        {
            /* Return to the beginning of the file. */
            result = fseek( file, 0L, SEEK_SET );

            if( result == -1 )
            {
                LogError( ( "Failed to move to beginning of certificate signing request file. Path: %s. Error: %s.",
                            PROVISIONING_CSR_PATH, strerror( errno ) ) );
                status = false;
            }
        }

        if( status == true )
        {
            size_t written = 0;
            /* Read the CSR into our buffer. */
            written = fread( buffer, 1, length, file );

            if( written != length )
            {
                LogError( ( "Failed reading certificate signing request file. Path: %s. Error: %s.",
                            PROVISIONING_CSR_PATH, strerror( errno ) ) );
                status = false;
            }
            else
            {
                *outCsrLength = length;
            }
        }

        fclose( file );
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool generateCsrRequest( char * buffer,
                                size_t bufferLength,
                                size_t * outLengthWritten )
{
    bool status = false;
    char csr[ NETWORK_BUFFER_SIZE ] = { 0 };
    size_t csrLength = 0;
    CborEncoder encoder, mapEncoder;
    CborError cborRet;

    status = getCsr( csr, NETWORK_BUFFER_SIZE, &csrLength );

    /* For details on the CreateCertificatefromCsr request payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#create-cert-csr-request-payload
     */
    if( status == true )
    {
        cbor_encoder_init( &encoder, ( uint8_t * ) buffer, bufferLength, 0 );
        cborRet = cbor_encoder_create_map( &encoder, &mapEncoder, 1 );

        if( cborRet == CborNoError )
        {
            cborRet = cbor_encode_text_stringz( &mapEncoder, "certificateSigningRequest" );
        }

        if( cborRet == CborNoError )
        {
            cborRet = cbor_encode_text_string( &mapEncoder, csr, csrLength );
        }

        if( cborRet == CborNoError )
        {
            cborRet = cbor_encoder_close_container( &encoder, &mapEncoder );
        }

        if( cborRet == CborNoError )
        {
            *outLengthWritten = cbor_encoder_get_buffer_size( &encoder, ( uint8_t * ) buffer );
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

static bool generateRegisterThingRequest( char * buffer,
                                          size_t bufferLength,
                                          const char * certificateOwnershipToken,
                                          size_t certificateOwnershipTokenLength,
                                          const char * serial,
                                          size_t serialLength,
                                          size_t * outLengthWritten )
{
    bool status = false;
    CborEncoder encoder, mapEncoder, parametersEncoder;
    CborError cborRet;

    /* For details on the RegisterThing request payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-request-payload
     */
    cbor_encoder_init( &encoder, ( uint8_t * ) buffer, bufferLength, 0 );
    cborRet = cbor_encoder_create_map( &encoder, &mapEncoder, 2 );

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &mapEncoder, "certificateOwnershipToken" );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_string( &mapEncoder, certificateOwnershipToken, certificateOwnershipTokenLength );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &mapEncoder, "parameters" );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encoder_create_map( &mapEncoder, &parametersEncoder, 1 );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_stringz( &parametersEncoder, "SerialNumber" );
    }

    if( cborRet == CborNoError )
    {
        cborRet = cbor_encode_text_string( &parametersEncoder, serial, serialLength );
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
        *outLengthWritten = cbor_encoder_get_buffer_size( &encoder, ( uint8_t * ) buffer );
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

static bool parseCsrResponse( const char * response,
                              size_t length,
                              char * certificate,
                              size_t * certificateLength,
                              char * certificateId,
                              size_t * certificateIdLength,
                              char * ownershipToken,
                              size_t * ownershipTokenLength )
{
    bool status = false;
    CborError cborRet;
    CborParser parser;
    CborValue map;
    CborValue value;

    /* For details on the CreateCertificatefromCsr response payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-response-payload
     */
    cborRet = cbor_parser_init( ( const uint8_t * ) response, length, 0, &parser, &map );

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
            cborRet = cbor_value_copy_text_string( &value, certificate, certificateLength, NULL );

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
            cborRet = cbor_value_copy_text_string( &value, certificateId, certificateIdLength, NULL );

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
            cborRet = cbor_value_copy_text_string( &value, ownershipToken, ownershipTokenLength, NULL );

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

static bool parseRegisterThingResponse( const char * response,
                                        size_t length,
                                        char * thingNameBuffer,
                                        size_t * thingNameBufferLength )
{
    bool status = true;
    CborError cborRet;
    CborParser parser;
    CborValue map;
    CborValue value;


    /* For details on the RegisterThing response payload format, see:
     * https://docs.aws.amazon.com/iot/latest/developerguide/fleet-provision-api.html#register-thing-response-payload
     */
    cborRet = cbor_parser_init( ( const uint8_t * ) response, length, 0, &parser, &map );

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
            cborRet = cbor_value_copy_text_string( &value, thingNameBuffer, thingNameBufferLength, NULL );

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

static bool waitForResponse( void )
{
    int i;
    bool status = false;

    responseStatus = ResponseNotReceived;

    for( i = 0; i < FLEET_PROV_RESPONSE_WAIT_SECONDS; i++ )
    {
        ( void ) ProcessLoop( 1000 );

        if( responseStatus != ResponseNotReceived )
        {
            break;
        }
    }

    if( responseStatus == ResponseNotReceived )
    {
        LogError( ( "Timed out waiting for response." ) );
    }

    if( responseStatus == ResponseAccepted )
    {
        status = true;
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool subscribeToCsrResponseTopics( void )
{
    bool status;

    status = SubscribeToTopic( FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC,
                               FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH );

    if( status == false )
    {
        LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                    FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH,
                    FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC ) );
    }

    if( status == true )
    {
        status = SubscribeToTopic( FP_CBOR_CREATE_CERT_REJECTED_TOPIC,
                                   FP_CBOR_CREATE_CERT_REJECTED_LENGTH );

        if( status == false )
        {
            LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                        FP_CBOR_CREATE_CERT_REJECTED_LENGTH,
                        FP_CBOR_CREATE_CERT_REJECTED_TOPIC ) );
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool unsubscribeFromCsrResponseTopics( void )
{
    bool status;

    status = UnsubscribeFromTopic( FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC,
                                   FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH );

    if( status == false )
    {
        LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                    FP_CBOR_CREATE_CERT_ACCEPTED_LENGTH,
                    FP_CBOR_CREATE_CERT_ACCEPTED_TOPIC ) );
    }

    if( status == true )
    {
        status = UnsubscribeFromTopic( FP_CBOR_CREATE_CERT_REJECTED_TOPIC,
                                       FP_CBOR_CREATE_CERT_REJECTED_LENGTH );

        if( status == false )
        {
            LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                        FP_CBOR_CREATE_CERT_REJECTED_LENGTH,
                        FP_CBOR_CREATE_CERT_REJECTED_TOPIC ) );
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool subscribeToRegisterThingResponseTopics( void )
{
    bool status;

    status = SubscribeToTopic( FP_CBOR_REGISTER_ACCEPTED_TOPIC( PROVISIONING_TEMPLATE_NAME ),
                               FP_CBOR_REGISTER_ACCEPTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ) );

    if( status == false )
    {
        LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                    FP_CBOR_REGISTER_ACCEPTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ),
                    FP_CBOR_REGISTER_ACCEPTED_TOPIC( PROVISIONING_TEMPLATE_NAME ) ) );
    }

    if( status == true )
    {
        status = SubscribeToTopic( FP_CBOR_REGISTER_REJECTED_TOPIC( PROVISIONING_TEMPLATE_NAME ),
                                   FP_CBOR_REGISTER_REJECTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ) );

        if( status == false )
        {
            LogError( ( "Failed to subscribe to fleet provisioning topic: %.*s.",
                        FP_CBOR_REGISTER_REJECTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ),
                        FP_CBOR_REGISTER_REJECTED_TOPIC( PROVISIONING_TEMPLATE_NAME ) ) );
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool unsubscribeFromRegisterThingResponseTopics( void )
{
    bool status;

    status = UnsubscribeFromTopic( FP_CBOR_REGISTER_ACCEPTED_TOPIC( PROVISIONING_TEMPLATE_NAME ),
                                   FP_CBOR_REGISTER_ACCEPTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ) );

    if( status == false )
    {
        LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                    FP_CBOR_REGISTER_ACCEPTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ),
                    FP_CBOR_REGISTER_ACCEPTED_TOPIC( PROVISIONING_TEMPLATE_NAME ) ) );
    }

    if( status == true )
    {
        status = UnsubscribeFromTopic( FP_CBOR_REGISTER_REJECTED_TOPIC( PROVISIONING_TEMPLATE_NAME ),
                                       FP_CBOR_REGISTER_REJECTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ) );

        if( status == false )
        {
            LogError( ( "Failed to unsubscribe from fleet provisioning topic: %.*s.",
                        FP_CBOR_REGISTER_REJECTED_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ),
                        FP_CBOR_REGISTER_REJECTED_TOPIC( PROVISIONING_TEMPLATE_NAME ) ) );
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool saveCertificate( const char * certificate,
                             size_t certificateLength )
{
    FILE * file;
    bool status = false;

    file = fopen( PROVISIONING_CERT_PATH, "wb" );

    if( file == NULL )
    {
        LogError( ( "Failed opening PROVISIONING_CERT_PATH for writing." ) );
    }
    else
    {
        size_t written;
        written = fwrite( ( const void * ) certificate, 1U, certificateLength, file );
        fclose( file );

        if( written != certificateLength )
        {
            LogError( ( "Failed writing certificate to file." ) );
        }
        else
        {
            status = true;
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

/* This example uses a single application task, which shows that how to use
 * the Fleet Provisioning library to generate and validate AWS IoT Fleet
 * Provisioning MQTT topics, and use the coreMQTT library to communicate with
 * the AWS IoT Fleet Provisioning APIs. */
int main( int argc,
          char ** argv )
{
    bool status = false;
    int exitStatus = EXIT_FAILURE;
    char serial[ 10 ];
    size_t serialLength = 10;
    /* Buffer for holding received certificate until it is saved. */
    char certificate[ CERT_BUFFER_LENGTH ];
    size_t certificateLength;
    /* Buffer for holding the certificate ID. */
    char certificateId[ CERT_ID_BUFFER_LENGTH ];
    size_t certificateIdLength;
    /* Buffer for holding the certificate ownership token. */
    char ownershipToken[ OWNERSHIP_TOKEN_BUFFER_LENGTH ];
    size_t ownershipTokenLength;
    bool connectionEstablished = false;
    size_t i;
    int demoRunCount = 0;

    /* Silence compiler warnings about unused variables. */
    ( void ) argc;
    ( void ) argv;

    do
    {
        /* Initialize the buffer lengths to their max lengths. */
        certificateLength = CERT_BUFFER_LENGTH;
        certificateIdLength = CERT_ID_BUFFER_LENGTH;
        ownershipTokenLength = OWNERSHIP_TOKEN_BUFFER_LENGTH;

        /* The demo template we use has a serial number as a parameter.
         * For this demo we use a random 10 digit number. */
        for( i = 0; i < serialLength; i++ )
        {
            serial[ i ] = '0' + ( rand() % 10 );
        }

        /* Create the document containing the CSR to publish to the
         * CreateCertificateFromCsr API. */
        status = generateCsrRequest( payloadBuffer, NETWORK_BUFFER_SIZE, &payloadLength );

        /**** Connect to AWS IoT Core with provisioning claim credentials *****/

        /* We first use the claim credentials to connect to the broker. These
         * credentials should allow use of the RegisterThing API and one of the
         * CreateCertificatefromCsr or CreateKeysAndCertificate.
         * In this demo we use CreateCertificatefromCsr. */
        if( status == true )
        {
            /* Attempts to connect to the AWS IoT MQTT broker over TCP. If the
             * connection fails, retries after a timeout. Timeout value will
             * exponentially increase until maximum attempts are reached. */
            LogInfo( ( "Establishing MQTT session with claim certificate..." ) );
            status = EstablishMqttSession( provisioningPublishCallback,
                                           CLAIM_CERT_PATH,
                                           CLAIM_PRIVATE_KEY_PATH );

            if( status == false )
            {
                LogError( ( "Failed to establish MQTT session." ) );
            }
            else
            {
                connectionEstablished = true;
            }
        }

        /**** Call the CreateCertificateFromCsr API ***************************/

        /* We use the CreateCertificatefromCsr API to obtain a client certificate
         * for a key on the device by means of sending a Certificate Signing
         * Request (CSR). */
        if( status == true )
        {
            /* Subscribe to the CreateCertificateFromCsr accepted and rejected
             * topics. In this demo we use CBOR, so we use the CBOR topics. */
            status = subscribeToCsrResponseTopics();
        }

        if( status == true )
        {
            /* Publish the CSR to the CreateCertificatefromCsr API. */
            PublishToTopic( FP_CBOR_CREATE_CERT_PUBLISH_TOPIC,
                            FP_CBOR_CREATE_CERT_PUBLISH_LENGTH,
                            payloadBuffer,
                            payloadLength );

            if( status == false )
            {
                LogError( ( "Failed to publish to fleet provisioning topic: %.*s.",
                            FP_CBOR_CREATE_CERT_PUBLISH_LENGTH,
                            FP_CBOR_CREATE_CERT_PUBLISH_TOPIC ) );
            }
        }

        if( status == true )
        {
            /* Get the response to the CreateCertificatefromCsr request. */
            status = waitForResponse();
        }

        if( status == true )
        {
            /* From the response, extract the certificate, certificate ID, and
             * certificate ownership token. */
            status = parseCsrResponse( payloadBuffer,
                                       payloadLength,
                                       certificate,
                                       &certificateLength,
                                       certificateId,
                                       &certificateIdLength,
                                       ownershipToken,
                                       &ownershipTokenLength );

            if( status == true )
            {
                LogInfo( ( "Received certificate with Id: %.*s", ( int ) certificateIdLength, certificateId ) );
            }
        }

        if( status == true )
        {
            /* Save the certificate where it is to be stored. In this demo we
             * save it to the file path given by #PROVISIONING_CERT_PATH */
            status = saveCertificate( certificate, certificateLength );
        }

        if( status == true )
        {
            /* Unsubscribe from the CreateCertificateFromCsr topics. */
            status = unsubscribeFromCsrResponseTopics();
        }

        /**** Call the RegisterThing API **************************************/

        /* We then use the RegisterThing API to activate the received certificate,
         * provision AWS IoT resources according to the provisioning template, and
         * receive device configuration. */
        if( status == true )
        {
            /* Create the document to publish to the RegisterThing API. */
            status = generateRegisterThingRequest( payloadBuffer,
                                                   NETWORK_BUFFER_SIZE,
                                                   ownershipToken,
                                                   ownershipTokenLength,
                                                   serial,
                                                   serialLength,
                                                   &payloadLength );
        }

        if( status == true )
        {
            /* Subscribe to the RegisterThing response topics. */
            status = subscribeToRegisterThingResponseTopics();
        }

        if( status == true )
        {
            /* Publish the RegisterThing request. */
            PublishToTopic( FP_CBOR_REGISTER_PUBLISH_TOPIC( PROVISIONING_TEMPLATE_NAME ),
                            FP_CBOR_REGISTER_PUBLISH_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ),
                            payloadBuffer,
                            payloadLength );

            if( status == false )
            {
                LogError( ( "Failed to publish to fleet provisioning topic: %.*s.",
                            FP_CBOR_REGISTER_PUBLISH_LENGTH( PROVISIONING_TEMPLATE_NAME_LENGTH ),
                            FP_CBOR_REGISTER_PUBLISH_TOPIC( PROVISIONING_TEMPLATE_NAME ) ) );
            }
        }

        if( status == true )
        {
            /* Get the response to the RegisterThing request. */
            status = waitForResponse();
        }

        if( status == true )
        {
            /* Extract the Thing name from the response. */
            thingNameLength = MAX_THING_NAME_LENGTH;
            status = parseRegisterThingResponse( payloadBuffer,
                                                 payloadLength,
                                                 thingName,
                                                 &thingNameLength );

            if( status == true )
            {
                LogInfo( ( "Received Thing name: %.*s", ( int ) thingNameLength, thingName ) );
            }
        }

        if( status == true )
        {
            /* Unsubscribe from the RegisterThing topics. */
            unsubscribeFromRegisterThingResponseTopics();
        }

        /**** Disconnect from AWS IoT Core ************************************/

        /* As we have completed the provisioning workflow, we disconnect from
         * the connection using the provisioning claim credentials. */
        if( connectionEstablished == true )
        {
            DisconnectMqttSession();
            connectionEstablished = false;
        }

        /**** Connect to AWS IoT Core with provisioned certificate ************/

        if( status == true )
        {
            LogInfo( ( "Establishing MQTT session with provisioned certificate..." ) );
            status = EstablishMqttSession( provisioningPublishCallback,
                                           PROVISIONING_CERT_PATH,
                                           PROVISIONING_PRIVATE_KEY_PATH );

            if( status != true )
            {
                LogError( ( "Failed to establish MQTT session." ) );
            }
            else
            {
                connectionEstablished = true;
            }
        }

        /**** Finish **********************************************************/

        if( connectionEstablished == true )
        {
            /* Close the connection. */
            DisconnectMqttSession();
            connectionEstablished = false;
        }

        if( status == true )
        {
            exitStatus = EXIT_SUCCESS;
        }

        /**** Retry in case of failure ****************************************/

        /* Increment the demo run count. */
        demoRunCount++;

        if( exitStatus == EXIT_SUCCESS )
        {
            LogInfo( ( "Demo iteration %d is successful.", demoRunCount ) );
        }
        /* Attempt to retry a failed iteration of demo for up to #FLEET_PROV_MAX_DEMO_LOOP_COUNT times. */
        else if( demoRunCount < FLEET_PROV_MAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %d failed. Retrying...", demoRunCount ) );
            sleep( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_SECONDS );
        }
        /* Failed all #FLEET_PROV_MAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", FLEET_PROV_MAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( exitStatus != EXIT_SUCCESS );

    /* Log demo success. */
    if( exitStatus == EXIT_SUCCESS )
    {
        LogInfo( ( "Demo completed successfully." ) );
        exitStatus = EXIT_SUCCESS;
    }

    return exitStatus;
}
/*-----------------------------------------------------------*/
