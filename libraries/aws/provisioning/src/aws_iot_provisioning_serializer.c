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
 * @file aws_iot_provisioning_serializer.c
 * @brief Implements the internal serializer functions of the Provisioning library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

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
 * @brief Wrapper for assert checking the passed serializer error code for `IOT_SERIALIZER_SUCCESS` value.
 *
 * This should be used for asserting serializer status codes when performing actual serialization into a buffer.
 *
 * @param[in] error The serializer error code to assert check.
 */
static bool _checkSuccess( IotSerializerError_t error );

/**
 * @brief Wrapper for assert checking the passed serializer error code for either `IOT_SERIALIZER_SUCCESS`
 * or `IOT_SERIALIZER_BUFFER_TOO_SMALL` values.
 *
 * This should be used for asserting serializer status codes when performing a serialization dry-run (i.e. serializing
 * without a buffer)
 * to calculate the total size of data that serialization will generate.
 *
 * @param[in] error The serializer error code to assert check.
 */
static bool _checkSuccessOrBufferToSmall( IotSerializerError_t error );

/**
 * @brief Performs serialization operations on the passed buffer for creating the MQTT request payload for the CreateKeysAndCertification operation.
 * @param[in] pOutermostEncoder The outermost encoder object to use for serialization.
 * @param[out] pSerializationBuffer The buffer to store the serialized payload data.
 * @param[in] bufferSize The size of the serialization buffer.
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if payload serialization is successful; otherwise #AWS_IOT_PROVISIONING_INTERNAL_FAILURE.
 */
static AwsIotProvisioningError_t _serializeCreateKeysAndCertificateRequestPayload( IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                                   uint8_t * pSerializationBuffer,
                                                                                   size_t bufferSize );

/**
 * @brief Performs serializes operations on the passed buffer for creating the MQTT request payload for the RegisterThing operation.
 * @param[in] pRequestData The data that will be serialized for sending with the request.
 * @param[in] pOutermostEncoder The outermost encoder object to use for serialization.
 * @param[out] pSerializationBuffer The buffer to store the serialized payload data.
 * @param[in] bufferSize The size of the serialization buffer.
 * @return Returns #AWS_IOT_PROVISIONING_SUCCESS if payload serialization is successful; otherwise #AWS_IOT_PROVISIONING_INTERNAL_FAILURE.
 */
static AwsIotProvisioningError_t _serializeRegisterThingRequestPayload( const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData,
                                                                        IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                        uint8_t * pSerializationBuffer,
                                                                        size_t bufferSize );

static bool _checkSuccess( IotSerializerError_t error )
{
    return( error == IOT_SERIALIZER_SUCCESS );
}

/*------------------------------------------------------------------*/

static bool _checkSuccessOrBufferToSmall( IotSerializerError_t error )
{
    return( error == IOT_SERIALIZER_SUCCESS || error == IOT_SERIALIZER_BUFFER_TOO_SMALL );
}

/*------------------------------------------------------------------*/

static AwsIotProvisioningError_t _serializeCreateKeysAndCertificateRequestPayload( IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                                   uint8_t * pSerializationBuffer,
                                                                                   size_t bufferSize )
{
    AwsIotProvisioning_Assert( pOutermostEncoder != NULL );
    IotSerializerEncoderObject_t emptyPayloadEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerError_t serializerStatus = IOT_SERIALIZER_SUCCESS;

    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );

    /* Determine the status checking expression logic for the serializer error code based on whether the serialization
     * buffer has been provided. This is done to accommodate #IOT_SERIALIZER_BUFFER_TOO_SMALL error when no
     * serialization buffer is provided. */
    bool (* checkSerializerStatus)( IotSerializerError_t );

    if( pSerializationBuffer == NULL )
    {
        checkSerializerStatus = _checkSuccessOrBufferToSmall;
    }
    else
    {
        checkSerializerStatus = _checkSuccess;
    }

    serializerStatus = _pAwsIotProvisioningEncoder->init( pOutermostEncoder,
                                                          pSerializationBuffer,
                                                          bufferSize );

    if( checkSerializerStatus( serializerStatus ) == false )
    {
        IotLogError( "Failed to initialize encoder for payload serialization of %s operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    /* Encode an empty map container (Diagnostic notation as "{}"") .*/
    serializerStatus = _pAwsIotProvisioningEncoder->openContainer( pOutermostEncoder,
                                                                   &emptyPayloadEncoder,
                                                                   0 );

    /* Close the map. */
    if( checkSerializerStatus( _pAwsIotProvisioningEncoder->closeContainer( pOutermostEncoder, &emptyPayloadEncoder ) ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*------------------------------------------------------------------*/

static AwsIotProvisioningError_t _serializeRegisterThingRequestPayload( const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData,
                                                                        IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                        uint8_t * pSerializationBuffer,
                                                                        size_t bufferSize )
{
    AwsIotProvisioning_Assert( ( pRequestData->pDeviceCertificateId != NULL ) && ( pRequestData->deviceCertificateIdLength > 0 ) );
    AwsIotProvisioning_Assert( ( pRequestData->pCertificateOwnershipToken != NULL ) && ( pRequestData->ownershipTokenLength > 0 ) );
    AwsIotProvisioning_Assert( ( ( pRequestData->pParametersStart == NULL ) && ( pRequestData->pParametersStart == 0 ) ) ||
                               ( ( pRequestData->pParametersStart != NULL ) && ( pRequestData->numOfParameters > 0 ) ) );

    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );

    IotSerializerEncoderObject_t outerMapEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t certificateIdData = IotSerializer_ScalarTextStringWithLength( pRequestData->pDeviceCertificateId,
                                                                                            pRequestData->deviceCertificateIdLength );
    IotSerializerScalarData_t certificateTokenData = IotSerializer_ScalarTextStringWithLength( pRequestData->pCertificateOwnershipToken,
                                                                                               pRequestData->ownershipTokenLength );
    IotSerializerEncoderObject_t parametersMapEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    size_t numOfPayloadEntries = 0;
    const AwsIotProvisioningRequestParameterEntry_t * pParametersList = pRequestData->pParametersStart;
    char * pParameterKeyCopy = NULL;
    IotSerializerScalarData_t parameterValueData;
    IotSerializerError_t serializerStatus = IOT_SERIALIZER_SUCCESS;

    /* If no parameters have been provided, then the payload map container will contain only 2 entries, one for
     * certificate ID and the other for for the certificate ownership token string.*/
    if( pParametersList == NULL )
    {
        numOfPayloadEntries = 2;
    }
    /* Otherwise, account for the entry of parameters as well in the count. */
    else
    {
        numOfPayloadEntries = 3;
    }

    /* Determine the status checking expression logic for the serializer error code based on whether the serialization
     * buffer has been provided. This is done to accommodate #IOT_SERIALIZER_BUFFER_TOO_SMALL error when no
     * serialization buffer is provided. */
    bool (* checkSerializerStatus)( IotSerializerError_t );

    if( pSerializationBuffer == NULL )
    {
        checkSerializerStatus = _checkSuccessOrBufferToSmall;
    }
    else
    {
        checkSerializerStatus = _checkSuccess;
    }

    serializerStatus = _pAwsIotProvisioningEncoder->init( pOutermostEncoder,
                                                          pSerializationBuffer,
                                                          bufferSize );

    if( checkSerializerStatus( serializerStatus ) == false )
    {
        IotLogError( "Failed to initialize encoder for payload serialization of %s operation",
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    /* Create the outermost map that will contain "certificate" and "parameters" (optional) entries .*/
    serializerStatus = _pAwsIotProvisioningEncoder->openContainer( pOutermostEncoder,
                                                                   &outerMapEncoder,
                                                                   numOfPayloadEntries );

    /* Insert the entry for the "certificate ID". */
    if( checkSerializerStatus( _pAwsIotProvisioningEncoder->appendKeyValue( &outerMapEncoder,
                                                                            PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_CERTIFICATE_ID_STRING,
                                                                            certificateIdData ) ) == false )
    {
        IotLogError( "Failed to encode entry keyed by %s in request payload of %s operation",
                     PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_CERTIFICATE_ID_STRING,
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    /* Insert the entry for the "certificate ownership token". */
    if( checkSerializerStatus( _pAwsIotProvisioningEncoder->appendKeyValue( &outerMapEncoder,
                                                                            PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_CERTIFICATE_TOKEN_STRING,
                                                                            certificateTokenData ) ) == false )
    {
        IotLogError( "Failed to encode entry keyed by %s in request payload of %s operation",
                     PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_CERTIFICATE_TOKEN_STRING,
                     REGISTER_THING_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    /* Insert entry for "parameters" data which will entail inserting a nested map. */
    if( pParametersList != NULL )
    {
        serializerStatus = _pAwsIotProvisioningEncoder->openContainerWithKey( &outerMapEncoder,
                                                                              PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_PARAMETERS_STRING,
                                                                              &parametersMapEncoder,
                                                                              pRequestData->numOfParameters );

        if( checkSerializerStatus( serializerStatus ) == false )
        {
            IotLogError( "Failed to encode entry keyed by %s in request payload of %s operation",
                         PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_PARAMETERS_STRING,
                         REGISTER_THING_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
        }

        /* Populate the nested map keyed by "parameters" with the entries passed. */
        for( size_t index = 0; index < pRequestData->numOfParameters; index++ )
        {
            parameterValueData = IotSerializer_ScalarTextStringWithLength( pParametersList[ index ].pParameterValue,
                                                                           pParametersList[ index ].parameterValueLength );

            /* Copy the key string to a buffer that we will terminate with the NULL character.
             * The list of parameters does NOT need to have NULL-terminated string members. */
            pParameterKeyCopy = AwsIotProvisioning_MallocString( pParametersList[ index ].parameterKeyLength * sizeof( char ) );
            strncpy( pParameterKeyCopy, pParametersList[ index ].pParameterKey, pParametersList[ index ].parameterKeyLength );

            /* Add the NULL terminator character after the copied string in the buffer, and cache the old value.
             * Note: This is done to accommodate the Unity Test Framework's implementation of malloc() which allocates
             * an extra "guard space" in the buffer beyond the requested size in the call. */
            char oldVal = pParameterKeyCopy[ pParametersList[ index ].parameterKeyLength ];
            pParameterKeyCopy[ pParametersList[ index ].parameterKeyLength ] = '\0';


            serializerStatus = _pAwsIotProvisioningEncoder->appendKeyValue( &parametersMapEncoder,
                                                                            pParameterKeyCopy,
                                                                            parameterValueData );

            /* Restore the original value in the key string buffer, at the location we inserted the NULL character,
             * before we release the buffer memory. */
            pParameterKeyCopy[ pParametersList[ index ].parameterKeyLength ] = oldVal;
            AwsIotProvisioning_FreeString( pParameterKeyCopy );

            if( checkSerializerStatus( serializerStatus ) == false )
            {
                IotLogError( "Failed to encode entry (key: %s, value: %s) in nested container keyed by %s for request payload of %s operation",
                             pParametersList[ index ].pParameterKey,
                             pParametersList[ index ].parameterKeyLength,
                             pParametersList[ index ].pParameterValue,
                             pParametersList[ index ].parameterValueLength,
                             PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_PARAMETERS_STRING,
                             REGISTER_THING_OPERATION_LOG );
                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
            }
        }

        /* Close the nested map container */
        if( checkSerializerStatus( _pAwsIotProvisioningEncoder->closeContainer( &outerMapEncoder, &parametersMapEncoder ) ) == false )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
        }
    }

    /* Close the map. */
    if( checkSerializerStatus( _pAwsIotProvisioningEncoder->closeContainer( pOutermostEncoder, &outerMapEncoder ) ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_PROVISIONING_INTERNAL_FAILURE );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*------------------------------------------------------------------*/

AwsIotProvisioningError_t _AwsIotProvisioning_SerializeCreateKeysAndCertificateRequestPayload( uint8_t ** pSerializationBuffer,
                                                                                               size_t * pBufferSize )
{
    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );
    IotSerializerEncoderObject_t outermostPayloadEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;
    *pBufferSize = 0;

    status = _serializeCreateKeysAndCertificateRequestPayload( &outermostPayloadEncoder, NULL, 0 );

    if( status != AWS_IOT_PROVISIONING_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Get the calculated required size. */
    *pBufferSize = _pAwsIotProvisioningEncoder->getExtraBufferSizeNeeded( &outermostPayloadEncoder );
    AwsIotProvisioning_Assert( *pBufferSize != 0 );

    /* Clean the encoder object handle. */
    _pAwsIotProvisioningEncoder->destroy( &outermostPayloadEncoder );

    /* Allocate memory for the request payload based on the size required from the dry-run of serialization */
    *pSerializationBuffer = AwsIotProvisioning_MallocPayload( *pBufferSize * sizeof( uint8_t ) );

    status = _serializeCreateKeysAndCertificateRequestPayload( &outermostPayloadEncoder,
                                                               *pSerializationBuffer,
                                                               *pBufferSize );

    if( status != AWS_IOT_PROVISIONING_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    _pAwsIotProvisioningEncoder->destroy( &outermostPayloadEncoder );

    IOT_FUNCTION_CLEANUP_END();
}

/*------------------------------------------------------------------*/

bool _AwsIotProvisioning_CalculateCertFromCsrPayloadSize( const char * pCertificateSigningRequest,
                                                          size_t csrLength,
                                                          size_t * pPayloadSize )
{
    ( void ) pCertificateSigningRequest;
    ( void ) csrLength;
    ( void ) pPayloadSize;

    return true;
}

/*------------------------------------------------------------------*/

bool _AwsIotProvisioning_SerializeCreateCertificateFromCsrRequestPayload( const char * pCertificateSigningRequest,
                                                                          size_t csrLength,
                                                                          uint8_t * pSerializationBuffer,
                                                                          size_t * pBufferSize )
{
    bool status = true;

    AwsIotProvisioning_Assert( pCertificateSigningRequest != NULL );
    AwsIotProvisioning_Assert( csrLength != 0 );
    AwsIotProvisioning_Assert( pBufferSize != NULL );

    if( pSerializationBuffer == NULL )
    {
        *pBufferSize = 0;
    }

    IotSerializerEncoderObject_t outerEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;
    IotSerializerEncoderObject_t mapEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t csrData = IotSerializer_ScalarTextStringWithLength( pCertificateSigningRequest,
                                                                                  csrLength );

    /* Determine the status checking expression logic for the serializer error code based on whether the serialization
     * buffer has been provided. This is done to accommodate #IOT_SERIALIZER_BUFFER_TOO_SMALL error when no
     * serialization buffer is provided. */
    bool (* isSuccessStatus)( IotSerializerError_t );

    if( pSerializationBuffer == NULL )
    {
        isSuccessStatus = _checkSuccessOrBufferToSmall;
    }
    else
    {
        isSuccessStatus = _checkSuccess;
    }

    if( isSuccessStatus( _pAwsIotProvisioningEncoder->init( &outerEncoder,
                                                            pSerializationBuffer,
                                                            *pBufferSize ) ) == false )
    {
        IotLogError( "serializer: Unable to serialize request payload: "
                     "Failed to initialize encoder: Operation={%s}",
                     CREATE_CERT_FROM_CSR_OPERATION_LOG );
        status = false;
    }

    if( status == true )
    {
        /* Encode the payload as a map container. */
        if( isSuccessStatus( _pAwsIotProvisioningEncoder->openContainer( &outerEncoder,
                                                                         &mapEncoder,
                                                                         1 ) ) == false )
        {
            IotLogError( "serializer: Unable to serialize payload: "
                         "Failed to open map container: Operation={%s}",
                         CREATE_CERT_FROM_CSR_OPERATION_LOG );
            status = false;
        }
    }

    if( status == true )
    {
        /* Encode the CSR string. */
        if( isSuccessStatus( _pAwsIotProvisioningEncoder->appendKeyValue( &mapEncoder,
                                                                          PROVISIONING_CREATE_CERT_FROM_CSR_REQUEST_PAYLOAD_PEM_STRING,
                                                                          csrData ) ) == false )


        {
            IotLogError( "serializer: Unable to serialize payload: "
                         "Failed to insert CSR entry in map: Operation={%s}",
                         CREATE_CERT_FROM_CSR_OPERATION_LOG );
            status = false;
        }

        /* Close the map.
         * Note: Always close the container, even if appendVKeyValue() fails,
         * to free the memory of the map encoder object.
         */
        if( isSuccessStatus( _pAwsIotProvisioningEncoder->closeContainer( &outerEncoder,
                                                                          &mapEncoder ) ) == false )
        {
            IotLogError( "serializer: Unable to serialize payload: "
                         "Failed to close map container: Operation={%s}",
                         CREATE_CERT_FROM_CSR_OPERATION_LOG );
            status = false;
        }
    }

    if( status == true )
    {
        /* If no payload buffer was passed, populate the calculated serialization size in the output parameter. */
        if( pSerializationBuffer == NULL )
        {
            *pBufferSize = _pAwsIotProvisioningEncoder->getExtraBufferSizeNeeded( &outerEncoder );
            AwsIotProvisioning_Assert( *pBufferSize != 0 );
            IotLogDebug( "serializer: Calculated serialization size and populated in output parameter: "
                         "Operation={%s}",
                         CREATE_CERT_FROM_CSR_OPERATION_LOG );
        }
    }

    _pAwsIotProvisioningEncoder->destroy( &outerEncoder );


    return status;
}

/*------------------------------------------------------------------*/

AwsIotProvisioningError_t _AwsIotProvisioning_SerializeRegisterThingRequestPayload( const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData,
                                                                                    uint8_t ** pSerializationBuffer,
                                                                                    size_t * pBufferSize )
{
    IOT_FUNCTION_ENTRY( AwsIotProvisioningError_t, AWS_IOT_PROVISIONING_SUCCESS );
    IotSerializerEncoderObject_t outermostPayloadEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_STREAM;
    *pBufferSize = 0;

    status = _serializeRegisterThingRequestPayload( pRequestData, &outermostPayloadEncoder, NULL, 0 );

    if( status != AWS_IOT_PROVISIONING_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Get the calculated required size. */
    *pBufferSize = _pAwsIotProvisioningEncoder->getExtraBufferSizeNeeded( &outermostPayloadEncoder );
    AwsIotProvisioning_Assert( *pBufferSize != 0 );

    /* Clean the encoder object handle. */
    _pAwsIotProvisioningEncoder->destroy( &outermostPayloadEncoder );

    /* Allocate memory for the request payload based on the size required from the dry-run of serialization */
    *pSerializationBuffer = AwsIotProvisioning_MallocPayload( *pBufferSize * sizeof( uint8_t ) );

    status = _serializeRegisterThingRequestPayload( pRequestData,
                                                    &outermostPayloadEncoder,
                                                    *pSerializationBuffer,
                                                    *pBufferSize );

    IOT_FUNCTION_CLEANUP_BEGIN();

    _pAwsIotProvisioningEncoder->destroy( &outermostPayloadEncoder );

    IOT_FUNCTION_CLEANUP_END();
}

/*------------------------------------------------------------------*/

size_t _AwsIotProvisioning_GenerateRegisterThingTopicFilter( const char * pTemplateName,
                                                             size_t templateNameLength,
                                                             char * pTopicFilterBuffer )
{
    AwsIotProvisioning_Assert( pTemplateName != NULL );
    AwsIotProvisioning_Assert( pTopicFilterBuffer != NULL );

    size_t filledBufferSize = 0;

    /* Generate the part of the topic string that is common to both request and response types. */
    ( void ) memcpy( pTopicFilterBuffer, PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX,
                     PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX_LENGTH );
    filledBufferSize += PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX_LENGTH;
    ( void ) memcpy( pTopicFilterBuffer + filledBufferSize, pTemplateName,
                     templateNameLength );
    filledBufferSize += templateNameLength;
    ( void ) memcpy( pTopicFilterBuffer + filledBufferSize,
                     PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX,
                     PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX_LENGTH );
    filledBufferSize += PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX_LENGTH;
    return filledBufferSize;
}
