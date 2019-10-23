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
 * @file aws_iot_onbording_parser.c
 * @brief Implements the internal functions for parsing server responses for the Onboarding library.
 */

/* The config header is always included first. */
#include "iot_config.h"

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

AwsIotOnboardingError_t _AwsIotOnboarding_ParseDeviceCredentialsResponse( const void * pDeviceCredentialsResponse,
                                                                          size_t deviceCredentialsResponseLength,
                                                                          const AwsIotOnboardingCallbackInfo_t * userCallbackInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );
    AwsIotOnboardingCallbackParam_t userCallbackParam = { 0 };

    IotSerializerDecoderObject_t payloadDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certificatePemDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t certificateIdDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t privateKeyDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    if( _pAwsIotOnboardingDecoder->init( &payloadDecoder,
                                         pDeviceCredentialsResponse,
                                         deviceCredentialsResponseLength ) !=
        IOT_SERIALIZER_SUCCESS )
    {
        /* Decoder object initialization failed */
        IotLogError(
            "Could not initialize decoder for parsing response from server of %s operation.",
            GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    if( payloadDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
    {
        IotLogError(
            "Invalid container type of response received from server of %s operation. Payload should be of map type.",
            GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                         ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
                                         &certificatePemDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Cannot find "certificatePem" */
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
                     GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( certificatePemDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is text string.",
            ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING,
            GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                         ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
                                         &certificateIdDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Cannot find "certificateId" */
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
                     GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( certificateIdDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" entry in server response of %s operation. Expected type is text string.",
            ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING,
            GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                         ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
                                         &privateKeyDecoder ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Cannot find "private key" */
        IotLogError( "Cannot find entry for \"%s\" in response from server of %s operation.",
                     ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
                     GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    if( privateKeyDecoder.type != IOT_SERIALIZER_SCALAR_BYTE_STRING )
    {
        IotLogError(
            "Invalid value type of \"%s\" data in server response of %s operation. Expected type is byte string.",
            ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING,
            GET_DEVICE_CREDENTIALS_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    /* Populate the data to be passed to the user callback.*/
    userCallbackParam.callbackType = AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE;
    userCallbackParam.u.deviceCredentialsInfo.pDeviceCertificate = ( const char * )
                                                                   certificatePemDecoder.u.value.u.string.pString;
    userCallbackParam.u.deviceCredentialsInfo.deviceCertificateLength =
        certificatePemDecoder.u.value.u.string.length;
    userCallbackParam.u.deviceCredentialsInfo.pCertificateId = ( const char * )
                                                               certificateIdDecoder.u.value.u.string.pString;
    userCallbackParam.u.deviceCredentialsInfo.certificateIdLength =
        certificateIdDecoder.u.value.u.string.length;
    userCallbackParam.u.deviceCredentialsInfo.pPrivateKey = ( const char * )
                                                            privateKeyDecoder.u.value.u.string.pString;
    userCallbackParam.u.deviceCredentialsInfo.privateKeyLength =
        privateKeyDecoder.u.value.u.string.length;

    /* Invoke the user-provided callback with the parsed credentials data . */
    userCallbackInfo->function( userCallbackInfo->userParam, &userCallbackParam );

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != AWS_IOT_ONBOARDING_INTERNAL_FAILURE )
    {
        _pAwsIotOnboardingDecoder->destroy( &payloadDecoder );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*------------------------------------------------------------------*/

AwsIotOnboardingError_t _AwsIotOnboarding_ParseOnboardDeviceResponse( const void * pResponsePayload,
                                                                      size_t responsePayloadLength,
                                                                      const AwsIotOnboardingCallbackInfo_t * userCallbackInfo )
{
    AwsIotOnboarding_Assert( pResponsePayload != NULL );
    AwsIotOnboarding_Assert( userCallbackInfo != NULL );

    IOT_FUNCTION_ENTRY( AwsIotOnboardingError_t, AWS_IOT_ONBOARDING_SUCCESS );
    AwsIotOnboardingCallbackParam_t userCallbackParam = { 0 };
    IotSerializerError_t decoderStatus = IOT_SERIALIZER_SUCCESS;
    IotSerializerDecoderObject_t payloadDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderObject_t deviceConfigurationDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
    IotSerializerDecoderIterator_t deviceConfigIter = IOT_SERIALIZER_DECODER_ITERATOR_INITIALIZER;
    size_t numOfDeviceConfigurationEntries = 0;
    AwsIotOnboardingResponseDeviceConfigurationEntry_t * pDeviceConfigurationList = NULL;
    bool configurationListAllocated = false;
    IotSerializerDecoderObject_t thingNameDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

    if( _pAwsIotOnboardingDecoder->init( &payloadDecoder,
                                         pResponsePayload,
                                         responsePayloadLength ) != IOT_SERIALIZER_SUCCESS )
    {
        /* Decoder object initialization failed */
        IotLogError(
            "Could not initialize decoder for parsing response from server of %s operation",
            GET_ONBOARD_DEVICE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }

    if( payloadDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
    {
        IotLogError(
            "Invalid container typeof  response received from server of %s operation. Payload should be of map type.",
            GET_ONBOARD_DEVICE_OPERATION_LOG );
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
    }

    decoderStatus = _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                                     ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                                                     &deviceConfigurationDecoder );

    /* Device Configuration entry NOT found in payload. */
    if( decoderStatus == IOT_SERIALIZER_NOT_FOUND )
    {
        IotLogDebug(
            "Device configuration data (searched with \"%s\" key) NOT present in server response for %s operation",
            ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
            GET_ONBOARD_DEVICE_OPERATION_LOG );
    }
    else if( decoderStatus != IOT_SERIALIZER_SUCCESS )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }
    /* Device Configuration entry FOUND in payload. */
    else
    {
        if( deviceConfigurationDecoder.type != IOT_SERIALIZER_CONTAINER_MAP )
        {
            IotLogError(
                "Invalid device configuration data received server response for %s operation. Data is expected to be encoded as map container.",
                GET_ONBOARD_DEVICE_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
        }

        /* Obtain the number of device configuration entries in the response, and allocate memory for the list of device
         * configuration data. */
        if( _pAwsIotOnboardingDecoder->getSizeOf( &deviceConfigurationDecoder, &numOfDeviceConfigurationEntries )
            != IOT_SERIALIZER_SUCCESS )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
        }

        pDeviceConfigurationList = AwsIotOnboarding_MallocDeviceConfigurationList( numOfDeviceConfigurationEntries *
                                                                                   sizeof( AwsIotOnboardingResponseDeviceConfigurationEntry_t ) );

        if( pDeviceConfigurationList == NULL )
        {
            IotLogError( "Failure in allocating memory for device configuration data in response payload of %s operation",
                         GET_ONBOARD_DEVICE_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_NO_MEMORY );
        }

        configurationListAllocated = true;

        /* Iterate over the contents of the device configuration to decode the list of configuration entries to pass to
         * the user-callback.*/
        if( _pAwsIotOnboardingDecoder->stepIn( &deviceConfigurationDecoder, &deviceConfigIter ) != IOT_SERIALIZER_SUCCESS )
        {
            IotLogError(
                "Failure in iterating inside the data keyed by %s within server response for %s operation.",
                ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                GET_ONBOARD_DEVICE_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
        }

        /* Decode each of the configuration entires and insert them in the list. */
        for( size_t configurationListIndex = 0; configurationListIndex < numOfDeviceConfigurationEntries; configurationListIndex++ )
        {
            IotSerializerDecoderObject_t deviceConfigInnerKeyDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;
            IotSerializerDecoderObject_t deviceConfigInnerValueDecoder = IOT_SERIALIZER_DECODER_OBJECT_INITIALIZER;

            /* Get the key and value of the map entry */
            if( ( _pAwsIotOnboardingDecoder->get( deviceConfigIter, &deviceConfigInnerKeyDecoder ) != IOT_SERIALIZER_SUCCESS ) ||
                ( _pAwsIotOnboardingDecoder->next( deviceConfigIter ) != IOT_SERIALIZER_SUCCESS ) ||
                ( _pAwsIotOnboardingDecoder->get( deviceConfigIter, &deviceConfigInnerValueDecoder ) != IOT_SERIALIZER_SUCCESS ) )
            {
                IotLogError(
                    "Failure in iterating inside entry of device configuration container (i.e. keyed by %s) within server response "
                    "for %s operation.",
                    ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                    GET_ONBOARD_DEVICE_OPERATION_LOG );
                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
            }

            pDeviceConfigurationList[ configurationListIndex ].pKey = ( const char * )
                                                                      deviceConfigInnerKeyDecoder.u.value.u.string.pString;
            pDeviceConfigurationList[ configurationListIndex ].keyLength = deviceConfigInnerKeyDecoder.u.value.u.string.length;

            pDeviceConfigurationList[ configurationListIndex ].pValue = ( const char * )
                                                                        deviceConfigInnerValueDecoder.u.value.u.string.pString;
            pDeviceConfigurationList[ configurationListIndex ].valueLength = deviceConfigInnerValueDecoder.u.value.u.string.length;

            _pAwsIotOnboardingDecoder->destroy( &deviceConfigInnerKeyDecoder );
            _pAwsIotOnboardingDecoder->destroy( &deviceConfigInnerValueDecoder );

            /* Advance to the next entry in the device configuration map. */
            if( _pAwsIotOnboardingDecoder->next( deviceConfigIter ) != IOT_SERIALIZER_SUCCESS )
            {
                IotLogError(
                    "Failure in iterating to the next pair of device configuration data within server response for %s operation.",
                    ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                    GET_ONBOARD_DEVICE_OPERATION_LOG );

                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
            }
        }

        if( _pAwsIotOnboardingDecoder->stepOut( deviceConfigIter, &deviceConfigurationDecoder ) != IOT_SERIALIZER_SUCCESS )
        {
            IotLogError(
                "Failure in stepping out of %s container data while decoding server response for %s operation.",
                ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING,
                GET_ONBOARD_DEVICE_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
        }
    }

    decoderStatus = _pAwsIotOnboardingDecoder->find( &payloadDecoder,
                                                     ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_THING_NAME_STRING,
                                                     &thingNameDecoder );

    /* Thing Name entry NOT found in payload. */
    if( decoderStatus == IOT_SERIALIZER_NOT_FOUND )
    {
        IotLogDebug(
            "Thing Name data (searched with \"%s\" key) NOT present in server response for %s operation",
            ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_THING_NAME_STRING,
            GET_ONBOARD_DEVICE_OPERATION_LOG );
    }
    else if( decoderStatus != IOT_SERIALIZER_SUCCESS )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_INTERNAL_FAILURE );
    }
    /* Thing Name entry FOUND in payload. */
    else
    {
        if( thingNameDecoder.type != IOT_SERIALIZER_SCALAR_TEXT_STRING )
        {
            IotLogError(
                "Invalid \"%s\" data received server response for %s operation. Value is expected to be a text string.",
                ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_THING_NAME_STRING,
                GET_ONBOARD_DEVICE_OPERATION_LOG );
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ONBOARDING_BAD_RESPONSE );
        }
    }

    /* Populate the data to be passed to the user callback.*/
    userCallbackParam.callbackType = ONBOARDING_ONBOARD_DEVICE;

    /* Populate information for the "Device Configuration" data. */
    userCallbackParam.u.onboardDeviceResponse.pDeviceConfigList = pDeviceConfigurationList;
    userCallbackParam.u.onboardDeviceResponse.numOfConfigurationEntries = numOfDeviceConfigurationEntries;

    /* Populate information for the "Thing Name" string. */
    userCallbackParam.u.onboardDeviceResponse.pThingName = ( const char * )
                                                           thingNameDecoder.u.value.u.string.pString;
    userCallbackParam.u.onboardDeviceResponse.thingNameLength = thingNameDecoder.u.value.u.string.length;

    /* Invoke the user-provided callback with the parsed credentials data . */
    userCallbackInfo->function( userCallbackInfo->userParam, &userCallbackParam );

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( configurationListAllocated == true )
    {
        AwsIotOnboarding_FreeDeviceConfigurationList( pDeviceConfigurationList );
    }

    _pAwsIotOnboardingDecoder->destroy( &deviceConfigurationDecoder );
    _pAwsIotOnboardingDecoder->destroy( &thingNameDecoder );
    _pAwsIotOnboardingDecoder->destroy( &payloadDecoder );

    IOT_FUNCTION_CLEANUP_END();
}
