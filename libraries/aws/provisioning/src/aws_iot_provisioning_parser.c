/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * @file aws_iot_provisioning_parser.c
 * @brief Implements the internal functions for parsing server responses for the Provisioning library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Error handling include. */
#include "iot_error.h"

/* Provisioning internal include. */
#include "private/aws_iot_provisioning_internal.h"

/* Logging module */
#include "iot_logging_setup.h"

/* Validate Provisioning configuration settings. */
#if AWS_IOT_PROVISIONING_ENABLE_ASSERTS != 0 && AWS_IOT_PROVISIONING_ENABLE_ASSERTS != 1
    #error "AWS_IOT_PROVISIONING_ENABLE_ASSERTS must be 0 or 1."
#endif

/*------------------------------------------------------------------*/

/**
 * @brief Parses the rejected response payload received from the server, and populates the data of the passed
 * @a pResponseData parameter.
 *
 * @param[in] pPayloadDecoder The outermost decoder object representing the response payload.
 * @param[in] pOperationName The Provisioning library operation (or API) that the response is associated with.
 * @param[out] pResponseData This will be populated with the data parsed from the response payload, if successful.
 * @param[out] pStatusCode This will be populated with the error status code parsed from the response payload,
 * if successful.
 *
 * @return #AWS_IOT_PROVISIONING_SUCCESS, if parsing is successful; otherwise appropriate error message.
 */
static AwsIotProvisioningError_t _parseRejectedResponse( IotSerializerDecoderObject_t * pPayloadDecoder,
                                                         const char * pOperationName,
                                                         AwsIotProvisioningRejectedResponse_t * pResponseData,
                                                         AwsIotProvisioningServerStatusCode_t * pStatusCode );

/**
 * @brief Utility for parsing a text-string based key-value pair entry from
 * from a map container type response payload.
 *
 * @param[in] payloadDecoder The decoder object representing the map container
 * formatted payload.
 * @param[in, out] payloadEntryDecoder The decoder object to store the parsed
 * value data of the entry.
 * @param[in] pKeyString The key string to parse from the payload.
 * @param[in] pOperationString The string of the ongoing operation to use for
 * logging.
 *
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if parsing is successful; otherwise
 * #AWS_IOT_PROVISIONING_BAD_RESPONSE if any of the expected data entries is missing
 * in the payload OR @AWS_IOT_PROVISIONING_INTERNAL_FAILURE for decoder failures.
 */
static AwsIotProvisioningError_t _parseKeyedEntryInPayload( IotSerializerDecoderObject_t * pPayloadDecoder,
                                                            IotSerializerDecoderObject_t * pPayloadEntryDecoder,
                                                            const char * pKeyString,
                                                            const char * pOperationString );

/**
 * @brief Common utility for parsing the Certificate PEM string, Certificate ID,
 * and Ownership token data from the server response.
 * These elements are common in the server responses of the MQTT CreateKeysAndCertificate
 * and CreateCertificateFromCsr APIs.
 *
 * @param[in] payloadDecoder The decoder object that represents the
 * server response payload as a map container.
 * @param[in/out] certPemDecoder The decoder object to store the parsed Certificate
 * PEM string in.
 * @param[in/out] certIdDecoder The decoder object to store the parsed
 * Certificate ID data in.
 * @param[in/out] ownershipTokenDecoder The decoder object to store the parsed
 * Certificate Ownership Token string in.
 * @param[in] pOperationString The string of the ongoing operation to use for
 * logging.
 *
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if parsing is successful; otherwise
 * #AWS_IOT_PROVISIONING_BAD_RESPONSE if any of the expected data entries is missing
 * in the payload OR @AWS_IOT_PROVISIONING_INTERNAL_FAILURE for decoder failures.
 */
static AwsIotProvisioningError_t _parseCommonCertInfoInResponse( IotSerializerDecoderObject_t * pPayloadDecoder,
                                                                 IotSerializerDecoderObject_t * pCertPemDecoder,
                                                                 IotSerializerDecoderObject_t * pCertIdDecoder,
                                                                 IotSerializerDecoderObject_t * pOwnershipTokenDecoder,
                                                                 const char * pOperationString );


static AwsIotProvisioningError_t _parseRejectedResponse( IotSerializerDecoderObject_t * pPayloadDecoder,
                                                         const char * pOperationName,
                                                         AwsIotProvisioningRejectedResponse_t * pResponseData,
                                                         AwsIotProvisioningServerStatusCode_t * pStatusCode )
{
    AwsIotProvisioning_Assert( pPayloadDecoder != NULL );
    AwsIotProvisioning_Assert( pPayloadDecoder->type == IOT_SERIALIZER_CONTAINER_MAP );
    AwsIotProvisioning_Assert( pResponseData != NULL );
    AwsIotProvisioning_Assert( pStatusCode != NULL );

    IotSerializerDecoderObject_t statusCodeDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t errorCodeDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t errorMessageDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    /* Suppress warning when parameter is unused in non-Debug mode. */
    ( void ) pOperationName;

    /* Initialize the status as "server refused" as we are parsing the "rejected" response. */
    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SERVER_REFUSED );

    /* Parse the "status code" information. */
    if( _pAwsIotProvisioningDecoder->find( pPayloadDecoder,
                                           PROVISIONING_REJECTED_RESPONSE_STATUS_CODE_STRING,
                                           &statusCodeDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     PROVISIONING_REJECTED_RESPONSE_STATUS_CODE_STRING,
                     pOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    if( statusCodeDecoder.type != IOT_SERIALIZER_SCALAR_SIGNED_INT )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is integer.",
            PROVISIONING_REJECTED_RESPONSE_STATUS_CODE_STRING,
            pOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    /* Copy the status code value to the output parameter. */
    *pStatusCode = ( AwsIotProvisioningServerStatusCode_t ) statusCodeDecoder.u.value.u.signedInt;

    /* Parse the "error code" information. */
    if( _pAwsIotProvisioningDecoder->find( pPayloadDecoder,
                                           PROVISIONING_REJECTED_RESPONSE_ERROR_CODE_STRING,
                                           &errorCodeDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
                     pOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    if( errorCodeDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is text string.",
            PROVISIONING_REJECTED_RESPONSE_ERROR_CODE_STRING,
            pOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    /* Store the error code information in the output parameter. */
    pResponseData->pErrorCode = ( const char * ) errorCodeDecoder.u.value.u.string.pString;
    pResponseData->errorCodeLength = errorCodeDecoder.u.value.u.string.length;

    /* Parse the "error message" information. */
    if( _pAwsIotProvisioningDecoder->find( pPayloadDecoder,
                                           PROVISIONING_REJECTED_RESPONSE_ERROR_MESSAGE_STRING,
                                           &errorMessageDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     PROVISIONING_REJECTED_RESPONSE_ERROR_MESSAGE_STRING,
                     pOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    if( errorMessageDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is text string.",
            PROVISIONING_REJECTED_RESPONSE_ERROR_MESSAGE_STRING,
            pOperationName );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    /* Store the error message information in the output parameter. */
    pResponseData->pErrorMessage = ( const char * ) errorMessageDecoder.u.value.u.string.pString;
    pResponseData->errorMessageLength = errorMessageDecoder.u.value.u.string.length;

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*------------------------------------------------------------------*/

static AwsIotProvisioningError_t _parseKeyedEntryInPayload( IotSerializerDecoderObject_t * pPayloadDecoder,
                                                            IotSerializerDecoderObject_t * pPayloadEntryDecoder,
                                                            const char * pKeyString,
                                                            const char * pOperationString )
{
    AwsIotProvisioning_Assert( pPayloadDecoder != NULL );
    AwsIotProvisioning_Assert( pPayloadEntryDecoder != NULL );
    AwsIotProvisioning_Assert( pKeyString != NULL );
    AwsIotProvisioning_Assert( pOperationString != NULL );

    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    IotSerializerError_t serializerStatus = IOT_SERIALIZER_SUCCESS;

    /* Look for the data entry in the map. */
    serializerStatus = _pAwsIotProvisioningDecoder->find( pPayloadDecoder,
                                                          pKeyString,
                                                          pPayloadEntryDecoder );

    if( serializerStatus == IOT_SERIALIZER_NOT_FOUND )
    {
        /* Entry not found in the payload map. */
        IotLogError( "parser: Unable to parse server response: Key entry not found in response:"
                     "ExpectedKey={\"%s\"}: Operation={%s}",
                     pKeyString,
                     pOperationString );
        status = AWS_IOT_PROVISIONING_BAD_RESPONSE;
    }
    else if( serializerStatus != IOT_SERIALIZER_SUCCESS )
    {
        status = AWS_IOT_PROVISIONING_INTERNAL_FAILURE;
    }
    else if( pPayloadEntryDecoder->type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "parser: Unable to parse server response: Invalid value type of key entry in payload: "
            "Expected type is text string: Key={\"%s\"}, Operation={%s}",
            pKeyString,
            pOperationString );
        status = AWS_IOT_PROVISIONING_BAD_RESPONSE;
    }
    else
    {
        /* Nothing to do. */
    }

    return status;
}

/*------------------------------------------------------------------*/

static AwsIotProvisioningError_t _parseCommonCertInfoInResponse( IotSerializerDecoderObject_t * pPayloadDecoder,
                                                                 IotSerializerDecoderObject_t * pCertPemDecoder,
                                                                 IotSerializerDecoderObject_t * pCertIdDecoder,
                                                                 IotSerializerDecoderObject_t * pOwnershipTokenDecoder,
                                                                 const char * pOperationString )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    AwsIotProvisioning_Assert( pPayloadDecoder != NULL );
    AwsIotProvisioning_Assert( pCertPemDecoder != NULL );
    AwsIotProvisioning_Assert( pCertIdDecoder != NULL );
    AwsIotProvisioning_Assert( pOwnershipTokenDecoder != NULL );

    /* Look for the certificate PEM data. */
    status = _parseKeyedEntryInPayload( pPayloadDecoder,
                                        pCertPemDecoder,
                                        PROVISIONING_SERVER_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
                                        pOperationString );

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Look for the certificate ID data. */
        status = _parseKeyedEntryInPayload( pPayloadDecoder,
                                            pCertIdDecoder,
                                            PROVISIONING_SERVER_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
                                            pOperationString );
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        /* Look for the certificate ownership token data. */
        status = _parseKeyedEntryInPayload( pPayloadDecoder,
                                            pOwnershipTokenDecoder,
                                            PROVISIONING_SERVER_RESPONSE_PAYLOAD_CERTIFICATE_TOKEN_KEY_STRING,
                                            pOperationString );
    }

    return status;
}

/*------------------------------------------------------------------*/

AwsIotProvisioningError_t _AwsIotProvisioning_ParseKeysAndCertificateResponse( AwsIotStatus_t responseType,
                                                                               const uint8_t * pResponsePayload,
                                                                               size_t payloadLength,
                                                                               const _provisioningCallbackInfo_t * userCallbackInfo )
{
    AwsIotProvisioning_Assert( pResponsePayload != NULL );
    AwsIotProvisioning_Assert( userCallbackInfo != NULL );

    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );
    AwsIotProvisioningCreateKeysAndCertificateResponse_t userCallbackParam =
        AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;

    IotSerializerDecoderObject_t payloadDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certPemDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certIdDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t privateKeyDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t ownershipTokenDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    if( _pAwsIotProvisioningDecoder->init( &payloadDecoder,
                                           pResponsePayload,
                                           payloadLength ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Decoder object initialization failed */
        IotLogError(
            "Could not initialize decoder for parsing response from server of %s operation.",
            CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    if( payloadDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
    {
        IotLogError(
            "Invalid container type of response received from server of %s operation. Payload should be of map type.",
            CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    switch( responseType )
    {
        case AWS_IOT_ACCEPTED:

            status = _parseCommonCertInfoInResponse( &payloadDecoder,
                                                     &certPemDecoder,
                                                     &certIdDecoder,
                                                     &ownershipTokenDecoder,
                                                     CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );

            if( status != AWS_IOT_PROVISIONING_SUCCESS )
            {
                IOT_GOTO_CLEANUP();
            }

            /* Look for the private Key data. */
            status = _parseKeyedEntryInPayload( &payloadDecoder,
                                                &privateKeyDecoder,
                                                PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
                                                CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG );

            if( status != AWS_IOT_PROVISIONING_SUCCESS )
            {
                IOT_GOTO_CLEANUP();
            }

            /* Populate the status code information to represent success response from the server. */
            userCallbackParam.statusCode = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED;

            /* Populate the data to be passed to the user callback.*/
            userCallbackParam.u.acceptedResponse.pDeviceCertificate = ( const char * )
                                                                      certPemDecoder.u.value.u.string.pString;
            userCallbackParam.u.acceptedResponse.deviceCertificateLength =
                certPemDecoder.u.value.u.string.length;
            userCallbackParam.u.acceptedResponse.pCertificateId = ( const char * )
                                                                  certIdDecoder.u.value.u.string.pString;
            userCallbackParam.u.acceptedResponse.certificateIdLength =
                certIdDecoder.u.value.u.string.length;
            userCallbackParam.u.acceptedResponse.pPrivateKey = ( const char * )
                                                               privateKeyDecoder.u.value.u.string.pString;
            userCallbackParam.u.acceptedResponse.privateKeyLength =
                privateKeyDecoder.u.value.u.string.length;

            userCallbackParam.u.acceptedResponse.pCertificateOwnershipToken = ( const char * )
                                                                              ownershipTokenDecoder.u.value.u.string.pString;
            userCallbackParam.u.acceptedResponse.ownershipTokenLength =
                ownershipTokenDecoder.u.value.u.string.length;

            /* Invoke the user-provided callback with the parsed credentials data . */
            userCallbackInfo->createKeysAndCertificateCallback.function( userCallbackInfo->createKeysAndCertificateCallback.userParam,
                                                                         &userCallbackParam );

            break;

        case AWS_IOT_REJECTED:
            status = _parseRejectedResponse( &payloadDecoder,
                                             REGISTER_THING_OPERATION_LOG,
                                             &userCallbackParam.u.rejectedResponse,
                                             &userCallbackParam.statusCode );

            /* Invoke the user-provided callback with the parsed rejected data, if parsing was successful . */
            if( status == AWS_IOT_PROVISIONING_SUCCESS )
            {
                userCallbackInfo->createKeysAndCertificateCallback.function( userCallbackInfo->createKeysAndCertificateCallback.userParam,
                                                                             &userCallbackParam );
            }

            break;

        default:
            IotLogError( "Unknown response type from the server for %s operation", REGISTER_THING_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
            AwsIotProvisioning_Assert( false );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != AWS_IOT_PROVISIONING_INTERNAL_FAILURE )
    {
        _pAwsIotProvisioningDecoder->destroy( &payloadDecoder );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*------------------------------------------------------------------*/

AwsIotProvisioningError_t _AwsIotProvisioning_ParseCsrResponse( AwsIotStatus_t responseType,
                                                                const uint8_t * pResponsePayload,
                                                                size_t payloadLength,
                                                                const _provisioningCallbackInfo_t * userCallbackInfo )
{
    AwsIotProvisioning_Assert( pResponsePayload != NULL );
    AwsIotProvisioning_Assert( userCallbackInfo != NULL );
    AwsIotProvisioning_Assert( ( responseType == AWS_IOT_REJECTED ) ||
                               ( responseType == AWS_IOT_ACCEPTED ) );

    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateCertFromCsrResponse_t userCallbackParam =
        AWS_IOT_PROVISIONING_CREATE_CERTIFICATE_FROM_CSR_CALLBACK_INFO_INITIALIZER;

    IotSerializerDecoderObject_t payloadDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certPemDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certIdDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t ownershipTokenDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    if( _pAwsIotProvisioningDecoder->init( &payloadDecoder,
                                           pResponsePayload,
                                           payloadLength ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Decoder object initialization failed */
        IotLogError(
            "parser: Unable to parser response: Failed to initialize decoder: Operation={%s}",
            CREATE_CERT_FROM_CSR_OPERATION_LOG );
        status = AWS_IOT_PROVISIONING_INTERNAL_FAILURE;
    }
    else if( payloadDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
    {
        IotLogError(
            "parser: Unable to parse server response: Payload format is invalid: "
            "Expected format is map container: Operation={%s}.",
            CREATE_CERT_FROM_CSR_OPERATION_LOG );
        status = AWS_IOT_PROVISIONING_BAD_RESPONSE;
    }

    if( status == AWS_IOT_PROVISIONING_SUCCESS )
    {
        if( responseType == AWS_IOT_ACCEPTED )
        {
            IotLogInfo( "parser: Server has ACCEPTED the operation request: Operation={%s}",
                        CREATE_CERT_FROM_CSR_OPERATION_LOG );

            status = _parseCommonCertInfoInResponse( &payloadDecoder,
                                                     &certPemDecoder,
                                                     &certIdDecoder,
                                                     &ownershipTokenDecoder,
                                                     CREATE_CERT_FROM_CSR_OPERATION_LOG );

            if( status == AWS_IOT_PROVISIONING_SUCCESS )
            {
                /* Populate the status code information to represent success response from the server. */
                userCallbackParam.statusCode = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED;

                /* Populate the data to be passed to the user callback.*/
                userCallbackParam.u.acceptedResponse.pDeviceCertificate = ( const char * )
                                                                          certPemDecoder.u.value.u.string.pString;
                userCallbackParam.u.acceptedResponse.deviceCertLength =
                    certPemDecoder.u.value.u.string.length;
                userCallbackParam.u.acceptedResponse.pCertId = ( const char * )
                                                               certIdDecoder.u.value.u.string.pString;
                userCallbackParam.u.acceptedResponse.certIdLength =
                    certIdDecoder.u.value.u.string.length;

                userCallbackParam.u.acceptedResponse.pCertOwnershipToken = ( const char * )
                                                                           ownershipTokenDecoder.u.value.u.string.pString;
                userCallbackParam.u.acceptedResponse.ownershipTokenLength =
                    ownershipTokenDecoder.u.value.u.string.length;

                /* Invoke the user-provided callback with the parsed credentials data . */
                IotLogInfo( "parser: About to call user-callback with accepted server response: Operation={%s}",
                            CREATE_CERT_FROM_CSR_OPERATION_LOG );
                userCallbackInfo->createCertFromCsrCallback.function( userCallbackInfo->createCertFromCsrCallback.userParam,
                                                                      &userCallbackParam );


                _pAwsIotProvisioningDecoder->destroy( &certPemDecoder );
                _pAwsIotProvisioningDecoder->destroy( &certIdDecoder );
                _pAwsIotProvisioningDecoder->destroy( &ownershipTokenDecoder );
            }
        }
        else if( responseType == AWS_IOT_REJECTED )
        {
            IotLogInfo( "parser: Server has REJECTED the operation request: Operation={%s}",
                        CREATE_CERT_FROM_CSR_OPERATION_LOG );

            status = _parseRejectedResponse( &payloadDecoder,
                                             REGISTER_THING_OPERATION_LOG,
                                             &userCallbackParam.u.rejectedResponse,
                                             &userCallbackParam.statusCode );

            /* Invoke the user-provided callback with the parsed rejected data, if parsing was successful . */
            if( status == AWS_IOT_PROVISIONING_SUCCESS )
            {
                IotLogInfo( "parser: About to call user-callback with rejected server response: Operation={%s}",
                            CREATE_CERT_FROM_CSR_OPERATION_LOG );
                userCallbackInfo->createCertFromCsrCallback.function( userCallbackInfo->createCertFromCsrCallback.userParam,
                                                                      &userCallbackParam );
            }
        }
    }

    _pAwsIotProvisioningDecoder->destroy( &payloadDecoder );

    return status;
}

/*------------------------------------------------------------------*/

AwsIotProvisioningError_t _AwsIotProvisioning_ParseRegisterThingResponse( AwsIotStatus_t responseType,
                                                                          const uint8_t * pResponsePayload,
                                                                          size_t responsePayloadLength,
                                                                          const _provisioningCallbackInfo_t * userCallbackInfo )
{
    AwsIotProvisioning_Assert( pResponsePayload != NULL );
    AwsIotProvisioning_Assert( userCallbackInfo != NULL );

    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );
    AwsIotProvisioningRegisterThingResponse_t userCallbackParam =
        AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;
    IotSerializerError_t decoderStatus = IOT_SERIALIZER_SUCCESS;
    IotSerializerDecoderObject_t payloadDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t deviceConfigurationDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderIterator_t deviceConfigIter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    size_t numOfDeviceConfigurationEntries = 0;
    AwsIotProvisioningResponseDeviceConfigurationEntry_t * pDeviceConfigurationList = NULL;
    bool configurationListAllocated = false;
    IotSerializerDecoderObject_t thingNameDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    if( _pAwsIotProvisioningDecoder->init( &payloadDecoder,
                                           pResponsePayload,
                                           responsePayloadLength ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Decoder object initialization failed */
        IotLogError(
            "Could not initialize decoder for parsing response from server of %s operation",
            REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    if( payloadDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
    {
        IotLogError(
            "Invalid container typeof  response received from server of %s operation. Payload should be of map type.",
            REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
    }

    switch( responseType )
    {
        case AWS_IOT_ACCEPTED:

            decoderStatus = _pAwsIotProvisioningDecoder->find( &payloadDecoder,
                                                               PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                                                               &deviceConfigurationDecoder );

            /* Device Configuration entry NOT found in payload. */
            if( decoderStatus == IOT_SERIALIZER_NOT_FOUND )
            {
                IotLogDebug(
                    "Device configuration data (searched with \"%s\" key) NOT present in server response for %s operation",
                    PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                    REGISTER_THING_OPERATION_LOG );
            }
            else if( decoderStatus != IOT_SERIALIZER_SUCCESS )
            {
                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
            }
            /* Device Configuration entry FOUND in payload. */
            else
            {
                if( deviceConfigurationDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
                {
                    IotLogError(
                        "Invalid device configuration data received in server response for %s operation. Data is expected to be encoded as map container.",
                        REGISTER_THING_OPERATION_LOG );
                    IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
                }

                /* Obtain the number of device configuration entries in the response, and allocate memory for the list
                 * of device configuration data. */
                if( _pAwsIotProvisioningDecoder->getSizeOf( &deviceConfigurationDecoder, &numOfDeviceConfigurationEntries )
                    != IOT_SERIALIZER_SUCCESS )
                {
                    IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
                }

                pDeviceConfigurationList = AwsIotProvisioning_MallocDeviceConfigurationList( numOfDeviceConfigurationEntries *
                                                                                             sizeof( AwsIotProvisioningResponseDeviceConfigurationEntry_t ) );

                if( pDeviceConfigurationList == NULL )
                {
                    IotLogError( "Failure in allocating memory for device configuration data in response payload of %s operation",
                                 REGISTER_THING_OPERATION_LOG );
                    IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_NO_MEMORY );
                }

                configurationListAllocated = true;

                /* Iterate over the contents of the device configuration to decode the list of configuration entries to
                 * pass to the user-callback.*/
                if( _pAwsIotProvisioningDecoder->stepIn( &deviceConfigurationDecoder, &deviceConfigIter ) != IOT_SERIALIZER_SUCCESS )
                {
                    IotLogError(
                        "Failure in iterating inside the data keyed by %s within server response for %s operation.",
                        PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                        REGISTER_THING_OPERATION_LOG );
                    IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
                }

                /* Decode each of the configuration entires and insert them in the list. */
                for( size_t configurationListIndex = 0; configurationListIndex < numOfDeviceConfigurationEntries; configurationListIndex++ )
                {
                    IotSerializerDecoderObject_t deviceConfigInnerKeyDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
                    IotSerializerDecoderObject_t deviceConfigInnerValueDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

                    /* Get the key and value of the map entry */
                    if( ( _pAwsIotProvisioningDecoder->get( deviceConfigIter, &deviceConfigInnerKeyDecoder ) != IOT_SERIALIZER_SUCCESS ) ||
                        ( _pAwsIotProvisioningDecoder->next( deviceConfigIter ) != IOT_SERIALIZER_SUCCESS ) ||
                        ( _pAwsIotProvisioningDecoder->get( deviceConfigIter, &deviceConfigInnerValueDecoder ) != IOT_SERIALIZER_SUCCESS ) )
                    {
                        IotLogError(
                            "Failure in iterating inside entry of device configuration container (i.e. keyed by %s) within server response "
                            "for %s operation.",
                            PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                            REGISTER_THING_OPERATION_LOG );
                        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
                    }

                    /* Validate that both the device configuration entry's key and value data are text strings. */
                    if( ( deviceConfigInnerKeyDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING ) ||
                        ( deviceConfigInnerValueDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING ) )
                    {
                        /**The serializer library allocates memory for the iterator. It can
                         * only be released by iterating to the last element in the map containers and "stepping out" of
                         * the container
                         * Thus, we will iterate to the end of the device configuration container to invalidate the
                         * iterator. */
                        size_t nextConfigEntryIndex = configurationListIndex + 1;

                        while( nextConfigEntryIndex < numOfDeviceConfigurationEntries )
                        {
                            _pAwsIotProvisioningDecoder->next( deviceConfigIter );
                            _pAwsIotProvisioningDecoder->next( deviceConfigIter );
                            nextConfigEntryIndex++;
                        }

                        /* Advance to the "end" of the container. */
                        _pAwsIotProvisioningDecoder->next( deviceConfigIter );
                        _pAwsIotProvisioningDecoder->stepOut( deviceConfigIter, &deviceConfigurationDecoder );

                        _pAwsIotProvisioningDecoder->destroy( &deviceConfigInnerKeyDecoder );
                        _pAwsIotProvisioningDecoder->destroy( &deviceConfigInnerValueDecoder );

                        IotLogError( "Invalid data type for device configuration entry received within server response for %s operation. Expected data"
                                     "type is text string for both keys and values.",
                                     REGISTER_THING_OPERATION_LOG );

                        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
                    }

                    pDeviceConfigurationList[ configurationListIndex ].pKey = ( const char * )
                                                                              deviceConfigInnerKeyDecoder.u.value.u.string.pString;
                    pDeviceConfigurationList[ configurationListIndex ].keyLength = deviceConfigInnerKeyDecoder.u.value.u.string.length;

                    pDeviceConfigurationList[ configurationListIndex ].pValue = ( const char * )
                                                                                deviceConfigInnerValueDecoder.u.value.u.string.pString;
                    pDeviceConfigurationList[ configurationListIndex ].valueLength = deviceConfigInnerValueDecoder.u.value.u.string.length;

                    _pAwsIotProvisioningDecoder->destroy( &deviceConfigInnerKeyDecoder );
                    _pAwsIotProvisioningDecoder->destroy( &deviceConfigInnerValueDecoder );

                    /* Advance to the next entry in the device configuration map. */
                    if( _pAwsIotProvisioningDecoder->next( deviceConfigIter ) != IOT_SERIALIZER_SUCCESS )
                    {
                        IotLogError(
                            "Failure in iterating to the next pair of device configuration data within server response for %s operation.",
                            PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                            REGISTER_THING_OPERATION_LOG );

                        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
                    }
                }

                if( _pAwsIotProvisioningDecoder->stepOut( deviceConfigIter, &deviceConfigurationDecoder ) != IOT_SERIALIZER_SUCCESS )
                {
                    IotLogError(
                        "Failure in stepping out of %s container data while decoding server response for %s operation.",
                        PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                        REGISTER_THING_OPERATION_LOG );
                    IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
                }
            }

            /* Look for the Thing Name entry. */
            decoderStatus = _pAwsIotProvisioningDecoder->find( &payloadDecoder,
                                                               PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_THING_NAME_STRING,
                                                               &thingNameDecoder );

            /* Thing Name entry NOT found in payload. */
            if( decoderStatus == IOT_SERIALIZER_NOT_FOUND )
            {
                IotLogDebug(
                    "Thing Name data (searched with \"%s\" key) NOT present in server response for %s operation",
                    PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_THING_NAME_STRING,
                    REGISTER_THING_OPERATION_LOG );
            }
            else if( decoderStatus != IOT_SERIALIZER_SUCCESS )
            {
                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
            }
            /* Thing Name entry FOUND in payload. */
            else
            {
                if( thingNameDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
                {
                    IotLogError(
                        "Invalid \"%s\" data received in server response for %s operation. Value is expected to be a text string.",
                        PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_THING_NAME_STRING,
                        REGISTER_THING_OPERATION_LOG );
                    IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_BAD_RESPONSE );
                }

                /* Populate information for the "Thing Name" string. */
                userCallbackParam.u.acceptedResponse.pThingName = ( const char * )
                                                                  thingNameDecoder.u.value.u.string.pString;
                userCallbackParam.u.acceptedResponse.thingNameLength = thingNameDecoder.u.value.u.string.length;
            }

            /* Populate the status code information to represent success response from the server. */
            userCallbackParam.statusCode = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED;

            /* Populate information for the "Device Configuration" data. */
            userCallbackParam.u.acceptedResponse.pDeviceConfigList = pDeviceConfigurationList;
            userCallbackParam.u.acceptedResponse.numOfConfigurationEntries = numOfDeviceConfigurationEntries;

            /* Invoke the user-provided callback with the parsed credentials data . */
            userCallbackInfo->registerThingCallback.function( userCallbackInfo->registerThingCallback.userParam,
                                                              &userCallbackParam );

            break;

        case AWS_IOT_REJECTED:
            status = _parseRejectedResponse( &payloadDecoder,
                                             REGISTER_THING_OPERATION_LOG,
                                             &userCallbackParam.u.rejectedResponse,
                                             &userCallbackParam.statusCode );

            /* Invoke the user-provided callback with the parsed rejected data, if parsing was successful . */
            if( status == AWS_IOT_PROVISIONING_SUCCESS )
            {
                userCallbackInfo->registerThingCallback.function( userCallbackInfo->registerThingCallback.userParam,
                                                                  &userCallbackParam );
            }

            break;

        default:
            IotLogError( "Unknown response type from the server for %s operation", REGISTER_THING_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
            AwsIotProvisioning_Assert( false );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( configurationListAllocated == true )
    {
        AwsIotProvisioning_FreeDeviceConfigurationList( pDeviceConfigurationList );
    }

    _pAwsIotProvisioningDecoder->destroy( &deviceConfigurationDecoder );
    _pAwsIotProvisioningDecoder->destroy( &thingNameDecoder );
    _pAwsIotProvisioningDecoder->destroy( &payloadDecoder );

    IOT_FUNCTION_CLEANUP_END();
}
