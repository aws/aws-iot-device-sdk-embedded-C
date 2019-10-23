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
 * @file aws_iot_onbording_serializer.c
 * @brief Implements the internal serializer functions of the Onboarding library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Error handling include. */
#include "iot_error.h"

/* Onboarding internal include. */
#include "private/aws_iot_onboarding_internal.h"

/* Logging module */
#include "iot_logging_setup.h"

/* Validate Onboarding configuration settings. */
#if AWS_IOT_ONBOARDING_ENABLE_ASSERTS != 0 && AWS_IOT_ONBOARDING_ENABLE_ASSERTS != 1
    #error "AWS_IOT_ONBOARDING_ENABLE_ASSERTS must be 0 or 1."
#endif

/*------------------------------------------------------------------*/

/**
 * @brief Wrapper for assert checking the passed serializer error code for #IOT_SERIALIZER_SUCCESS value.
 *
 * This should be used for asserting serializer status codes when performing actual serialization into a buffer.
 *
 * @param[in] error The serializer error code to assert check.
 */
static bool _checkSuccess( IotSerializerError_t error );

/**
 * @brief Wrapper for assert checking the passed serializer error code for either #IOT_SERIALIZER_SUCCESS
 * or #IOT_SERIALIZER_BUFFER_TOO_SMALL values.
 *
 * This should be used for asserting serializer status codes when performing a serialization dry-run (i.e. serializing
 * without a buffer)
 * to calculate the total size of data that serialization will generate.
 *
 * @param[in] error The serializer error code to assert check.
 */
static bool _checkSuccessOrBufferToSmall( IotSerializerError_t error );

static bool _checkSuccess( IotSerializerError_t error )
{
    return( error == IOT_SERIALIZER_SUCCESS );
}

static bool _checkSuccessOrBufferToSmall( IotSerializerError_t error )
{
    return( error == IOT_SERIALIZER_SUCCESS || error ==
            IOT_SERIALIZER_BUFFER_TOO_SMALL );
}

/*------------------------------------------------------------------*/

AwsIotOnboardingError_t _AwsIotOnboarding_SerializeGetDeviceCredentialsRequestPayload( IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                                       uint8_t * pSerializationBuffer,
                                                                                       size_t bufferSize )
{
    AwsIotOnboarding_Assert( pOutermostEncoder != NULL );
    IotSerializerEncoderObject_t emptyPayloadEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerError_t serializerStatus = IOT_SERIALIZER_SUCCESS;

    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );

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

    serializerStatus = _pAwsIotOnboardingEncoder->init( pOutermostEncoder,
                                                        pSerializationBuffer,
                                                        bufferSize );

    if( checkSerializerStatus( serializerStatus ) == false )
    {
        IotLogError( "Failed to initialize encoder for payload serialization of %s operation",
                     GET_ONBOARD_DEVICE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    /* Encode an empty map container (Diagnostic notation as "{}"") .*/
    serializerStatus = _pAwsIotOnboardingEncoder->openContainer( pOutermostEncoder,
                                                                 &emptyPayloadEncoder,
                                                                 0 );

    /* Close the map. */
    if( checkSerializerStatus( _pAwsIotOnboardingEncoder->closeContainer( pOutermostEncoder, &emptyPayloadEncoder ) ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_PARAMETER );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}


/*------------------------------------------------------------------*/

AwsIotOnboardingError_t _AwsIotOnboarding_SerializeOnboardDeviceRequestPayload( const AwsIotOnboardingOnboardDeviceRequestInfo_t * pRequestData,
                                                                                IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                                uint8_t * pSerializationBuffer,
                                                                                size_t bufferSize )
{
    AwsIotOnboarding_Assert( ( pRequestData->pDeviceCertificateId != NULL ) && ( pRequestData->deviceCertificateIdLength > 0 ) );
    AwsIotOnboarding_Assert( ( ( pRequestData->pParametersStart == NULL ) && ( pRequestData->pParametersStart == 0 ) ) ||
                             ( ( pRequestData->pParametersStart != NULL ) && ( pRequestData->numOfParameters > 0 ) ) );

    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );

    IotSerializerEncoderObject_t outerMapEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    IotSerializerScalarData_t certificateIdData = IotSerializer_ScalarTextStringWithLength( pRequestData->pDeviceCertificateId,
                                                                                            pRequestData->deviceCertificateIdLength );
    IotSerializerEncoderObject_t parametersMapEncoder = IOT_SERIALIZER_ENCODER_CONTAINER_INITIALIZER_MAP;
    size_t numOfPayloadEntries = 2;
    const AwsIotOnboardingRequestParameterEntry_t * pParametersList = pRequestData->pParametersStart;
    char * pParameterKeyCopy = NULL;
    IotSerializerScalarData_t parameterValueData;
    IotSerializerError_t serializerStatus = IOT_SERIALIZER_SUCCESS;

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

    serializerStatus = _pAwsIotOnboardingEncoder->init( pOutermostEncoder,
                                                        pSerializationBuffer,
                                                        bufferSize );

    if( checkSerializerStatus( serializerStatus ) == false )
    {
        IotLogError( "Failed to initialize encoder for payload serialization of %s operation",
                     GET_ONBOARD_DEVICE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    /* If no parameters have been passed, then the payload map will contain only a single entry (i.e. for certificate).
     * */
    if( pParametersList == NULL )
    {
        numOfPayloadEntries = 1;
    }

    /* Create the outermost map that will contain "certificate" and "parameters" (optional) entries .*/
    serializerStatus = _pAwsIotOnboardingEncoder->openContainer( pOutermostEncoder,
                                                                 &outerMapEncoder,
                                                                 numOfPayloadEntries );

    /* Insert the entry for the "certificate". */
    if( checkSerializerStatus( _pAwsIotOnboardingEncoder->appendKeyValue( &outerMapEncoder,
                                                                          ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_CERTIFICATE_ID_STRING,
                                                                          certificateIdData ) ) == false )
    {
        IotLogError( "Failed to encode entry keyed by %s in request payload of %s operation",
                     ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_CERTIFICATE_ID_STRING,
                     GET_ONBOARD_DEVICE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    /* Insert entry for "parameters" data which will entail inserting a nested map. */
    if( pParametersList != NULL )
    {
        serializerStatus = _pAwsIotOnboardingEncoder->openContainerWithKey( &outerMapEncoder,
                                                                            ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_PARAMETERS_STRING,
                                                                            &parametersMapEncoder,
                                                                            pRequestData->numOfParameters );

        if( checkSerializerStatus( serializerStatus ) == false )
        {
            IotLogError( "Failed to encode entry keyed by %s in request payload of %s operation",
                         ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_PARAMETERS_STRING,
                         GET_ONBOARD_DEVICE_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
        }

        /* Populate the nested map keyed by "parameters" with the entries passed. */
        for( size_t index = 0; index < pRequestData->numOfParameters; index++ )
        {
            parameterValueData = IotSerializer_ScalarTextStringWithLength( pParametersList[ index ].pParameterValue,
                                                                           pParametersList[ index ].parameterValueLength );

            /* Copy the key string to a buffer that we will terminate with the NULL character.
             * The parameters list does NOT need to have NULL-terminated string members. */
            pParameterKeyCopy = AwsIotOnboarding_MallocString( pParametersList[ index ].parameterKeyLength * sizeof( char ) );
            strncpy( pParameterKeyCopy, pParametersList[ index ].pParameterKey, pParametersList[ index ].parameterKeyLength );

            /* Add the NULL terminator character after the copied string in the buffer, and cache the old value.
             * Note: This is done to accommodate the Unity Test Framework's implementation of malloc() which allocates
             * an extra "guard space" in the buffer beyond the requested size in the call. */
            char oldVal = pParameterKeyCopy[ pParametersList[ index ].parameterKeyLength ];
            pParameterKeyCopy[ pParametersList[ index ].parameterKeyLength ] = '\0';


            serializerStatus = _pAwsIotOnboardingEncoder->appendKeyValue( &parametersMapEncoder,
                                                                          pParameterKeyCopy,
                                                                          parameterValueData );

            /* Restore the original value in the key string buffer, at the location we inserted the NULL character,
             * before we release the buffer memory. */
            pParameterKeyCopy[ pParametersList[ index ].parameterKeyLength ] = oldVal;
            AwsIotOnboarding_FreeString( pParameterKeyCopy );

            if( checkSerializerStatus( serializerStatus ) == false )
            {
                IotLogError( "Failed to encode entry (key: %s, value: %s) in nested container keyed by %s for request payload of %s operation",
                             pParametersList[ index ].pParameterKey,
                             pParametersList[ index ].parameterKeyLength,
                             pParametersList[ index ].pParameterValue,
                             pParametersList[ index ].parameterValueLength,
                             ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_PARAMETERS_STRING,
                             GET_ONBOARD_DEVICE_OPERATION_LOG );
                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
            }
        }

        /* Close the nested map container */
        if( checkSerializerStatus( _pAwsIotOnboardingEncoder->closeContainer( &outerMapEncoder, &parametersMapEncoder ) ) == false )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_PARAMETER );
        }
    }

    /* Close the map. */
    if( checkSerializerStatus( _pAwsIotOnboardingEncoder->closeContainer( pOutermostEncoder, &outerMapEncoder ) ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_PARAMETER );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*------------------------------------------------------------------*/

size_t _AwsIotOnboarding_GenerateOnboardDeviceTopicFilter( const char * pTemplateIdentifier,
                                                           size_t templateIdentifierLength,
                                                           char * pTopicFilterBuffer )
{
    AwsIotOnboarding_Assert( pTemplateIdentifier != NULL );
    AwsIotOnboarding_Assert( pTopicFilterBuffer != NULL );

    size_t filledBufferSize = 0;

    /* Generate the part of the topic string that is common to both request and response types. */
    ( void ) memcpy( pTopicFilterBuffer, ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX,
                     ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX_LENGTH );
    filledBufferSize += ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX_LENGTH;
    ( void ) memcpy( pTopicFilterBuffer + filledBufferSize, pTemplateIdentifier,
                     templateIdentifierLength );
    filledBufferSize += templateIdentifierLength;
    ( void ) memcpy( pTopicFilterBuffer + filledBufferSize,
                     ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX,
                     ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX_LENGTH );
    filledBufferSize += ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX_LENGTH;
    return filledBufferSize;
}
