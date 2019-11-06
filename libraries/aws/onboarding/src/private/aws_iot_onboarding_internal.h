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
 * @file aws_iot_onboarding_internal.h
 * @brief Internal header of Onboarding library. This header should not be included in
 * typical application code.
 */

#ifndef AWS_IOT_ONBOARDING_INTERNAL_H_
#define AWS_IOT_ONBOARDING_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* AWS IoT common header include. */
#include "aws_iot.h"

/* Onboarding include. */
#include "aws_iot_onboarding.h"

/* Serializer include. */
#include "iot_serializer.h"

/**
 * @def AwsIotOnboarding_Assert( expression )
 * @brief Assertion macro for the Onboarding library.
 *
 * Set @ref AWS_IOT_ONBOARDING_ENABLE_ASSERTS to `1` to enable assertions in the Onboarding
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if AWS_IOT_ONBOARDING_ENABLE_ASSERTS == 1
    #ifndef AwsIotOnboarding_Assert
        #ifdef Iot_DefaultAssert
            #define AwsIotOnboarding_Assert( expression )    Iot_DefaultAssert( expression )
        #else
            #error "Asserts are enabled for MQTT, but AwsIotOnboarding_Assert is not defined"
        #endif
    #endif
#else
    #define AwsIotOnboarding_Assert( expression )
#endif

/* Configure logs for ONBOARDING functions. */
#ifdef AWS_IOT_LOG_LEVEL_ONBOARDING
    #define LIBRARY_LOG_LEVEL        AWS_IOT_LOG_LEVEL_ONBOARDING
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "Onboarding" )
#include "iot_logging_setup.h"

/**
 * @brief Printable names for each of the Onboarding operations.
 */
#define GET_DEVICE_CREDENTIALS_OPERATION_LOG    "GET DEVICE CREDENTIALS"
#define GET_ONBOARD_DEVICE_OPERATION_LOG        "ONBOARD DEVICE"


#ifndef AWS_IOT_ONBOARDING_FORMAT
    #define AWS_IOT_ONBOARDING_FORMAT    AWS_IOT_ONBOARDING_FORMAT_CBOR
#endif

/* In current release, JSON format is not supported. */
#if AWS_IOT_ONBOARDING_FORMAT == AWS_IOT_ONBOARDING_FORMAT_JSON
    #error "AWS_IOT_ONBOARDING_FORMAT_JSON is not supported."
#endif

/**
 * Define encoder/decoder based on configuration AWS_IOT_ONBOARDING_FORMAT.
 */
#if AWS_IOT_ONBOARDING_FORMAT == AWS_IOT_ONBOARDING_FORMAT_CBOR
    #define ONBOARDING_FORMAT    "cbor"
#else /* if AWS_IOT_ONBOARDING_FORMAT == AWS_IOT_ONBOARDING_FORMAT_CBOR */
    #error "AWS_IOT_ONBOARDING_FORMAT must be AWS_IOT_ONBOARDING_FORMAT_CBOR."
#endif /* if AWS_IOT_ONBOARDING_FORMAT == AWS_IOT_ONBOARDING_FORMAT_CBOR */

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "iot_static_memory.h"

/**
 * @brief Allocate an . This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotOnboarding_MallocPayload    Iot_MallocMessageBuffer

/**
 * @brief Free an . This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotOnboarding_FreePayload      Iot_FreeMessageBuffer

/**
 * @brief Allocate an . This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotOnboarding_MallocString     Iot_MallocMessageBuffer

/**
 * @brief Free an . This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotOnboarding_FreeString       Iot_FreeMessageBuffer


/**
 * @brief Allocate an . This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotOnboarding_MallocDeviceConfigurationList    Iot_MallocMessageBuffer

/**
 * @brief Free an . This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotOnboarding_FreeDeviceConfigurationList      Iot_FreeMessageBuffer


#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #ifndef AwsIotOnboarding_MallocPayload
        #ifdef Iot_DefaultMalloc
            #define AwsIotOnboarding_MallocPayload    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for AwsIotOnboarding_MallocPayload"
        #endif
    #endif

    #ifndef AwsIotOnboarding_FreePayload
        #ifdef Iot_DefaultFree
            #define AwsIotOnboarding_FreePayload    Iot_DefaultFree
        #else
            #error "No Free function defined for AwsIotOnboarding_FreePayload"
        #endif
    #endif

    #ifndef AwsIotOnboarding_MallocString
        #ifdef Iot_DefaultMalloc
            #define AwsIotOnboarding_MallocString    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for AwsIotOnboarding_MallocString"
        #endif
    #endif

    #ifndef AwsIotOnboarding_FreeString
        #ifdef Iot_DefaultFree
            #define AwsIotOnboarding_FreeString    Iot_DefaultFree
        #else
            #error "No Free function defined for AwsIotOnboarding_FreeString"
        #endif
    #endif

    #ifndef AwsIotOnboarding_MallocDeviceConfigurationList
        #ifdef Iot_DefaultMalloc
            #define AwsIotOnboarding_MallocDeviceConfigurationList    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for "
            "AwsIotOnboarding_MallocDeviceConfigurationList"
        #endif
    #endif

    #ifndef AwsIotOnboarding_FreeDeviceConfigurationList
        #ifdef Iot_DefaultFree
            #define AwsIotOnboarding_FreeDeviceConfigurationList    Iot_DefaultFree
        #else
            #error "No Free function defined for "
            "AwsIotOnboarding_FreeDeviceConfigurationList"
        #endif
    #endif

#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS
    #define AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS    ( 5000 )
#endif
/** @endcond */

/**
 * @brief The MQTT response topic filter for the GetDeviceCredentials service API.
 *
 * @note The complete response topics are suffixed with #AWS_IOT_ACCEPTED_SUFFIX or #AWS_IOT_REJECTED_SUFFIX strings.
 * It should be utilized in the @ref onboarding_function_getdevicecredentials API function.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER \
    "$aws/certificates/create/"ONBOARDING_FORMAT

/**
 * @brief Length of the MQTT response topic filtert for the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER_LENGTH \
    ( ( uint16_t ) ( sizeof( ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER ) - 1 ) )

/**
 * @brief The length of the longest MQTT response topic of the GetDeviceCredentials service API.
 * Out of the two response topics, the "rejected" has the longest length.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_MAX_TOPIC_LENGTH    \
    ( ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER_LENGTH + \
      sizeof( AWS_IOT_REJECTED_SUFFIX ) )


/**
 * @brief The MQTT request topic for the GetDeviceCredentials service API.
 *
 * @note It should be utilized in the @ref onboarding_function_getdevicecredentials API function.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC \
    "$aws/certificates/create/"ONBOARDING_FORMAT

/**
 * @brief The length of the MQTT request topic for the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC_LENGTH \
    ( ( uint16_t ) ( sizeof( ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC ) - 1 ) )

/**
 * @brief The key for the device certificate entry in the response payload of the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING    "certificatePem"

/**
 * @brief The key for the certificate Id entry in the response payload of the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING     "certificateId"

/**
 * @brief The key for the private key entry in the response payload of the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING        "privateKey"

/**
 * @brief The common path in the request and response MQTT topics of the OnboardDevice service API.
 */
#define ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX \
    "$aws/provisioning-templates/"

/**
 * @brief The length of the common path in the request and response MQTT topics of the OnboardDevice service API.
 */
#define ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX_LENGTH \
    ( ( uint16_t ) ( sizeof( ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX ) - 1 ) )

/**
 * @brief The length of the Template ID text in the MQTT topics of the OnboardDevice service API.
 *
 * @note The Template ID follows the UUID (Universally Unique Identifier) format.
 */
#define ONBOARDING_TEMPLATE_ID_LENGTH                     ( 36 )

/**
 * @brief The common suffix in the request and response MQTT topics of the OnboardDevice service API.
 */
#define ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX    "/register/"ONBOARDING_FORMAT

/**
 * @brief The length of the common suffix in the MQTT topics of the OnboardDevice service API.
 */
#define ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX_LENGTH \
    ( ( uint16_t ) ( sizeof( ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX ) - 1 ) )


/**
 * @brief The length of the complete MQTT request topic of the OnboardDevice service API.
 */
#define ONBOARDING_ONBOARD_DEVICE_REQUEST_TOPIC_LENGTH                                        \
    ( ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX_LENGTH + ONBOARDING_TEMPLATE_ID_LENGTH + \
      ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX_LENGTH )

/**
 * @brief The key for the certificate ID's entry to be inserted in the request payload for the OnboardDevice service
 * API.
 *
 * @note This should be used in serializing the request payload for sending to the server.
 */
#define ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_CERTIFICATE_ID_STRING    "certificateId"

/**
 * @brief The key for the device context data's entry to be inserted in the request payload for the OnboardDevice
 * service API.
 *
 * @note This should be used in serializing the request payload for sending to the server, only if the calling
 * application provides valid device context data.
 */
#define ONBOARDING_ONBOARD_DEVICE_REQUEST_PAYLOAD_PARAMETERS_STRING        "deviceContext"

/**
 * @brief The length of the MQTT request topic filter of the OnboardDevice service API.
 */
#define ONBOARDING_ONBOARD_DEVICE_RESPONSE_TOPIC_FILTER_LENGTH                                \
    ( ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_PREFIX_LENGTH + ONBOARDING_TEMPLATE_ID_LENGTH + \
      ONBOARDING_ONBOARD_DEVICE_TOPICS_COMMON_SUFFIX_LENGTH )

/**
 * @brief The length of the longest MQTT response topic of the OnboardDevice service API.
 * Out of the two response topics, the "rejected" has the longest length.
 */
#define ONBOARDING_ONBOARD_DEVICE_RESPONSE_MAX_TOPIC_LENGTH \
    ( ONBOARDING_ONBOARD_DEVICE_RESPONSE_TOPIC_FILTER_LENGTH + sizeof( AWS_IOT_REJECTED_SUFFIX ) )

/**
 * @brief The key for the device configuration data's entry in the response payload of the OnboardDevice service API.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING    "deviceConfiguration"

/**
 * @brief The key for the Thing resource name's entry in the response payload of the OnboardDevice service API.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define ONBOARDING_ONBOARD_DEVICE_RESPONSE_PAYLOAD_THING_NAME_STRING              "thingName"

/**
 * @brief The key for the status code entry in the "rejected" response payload from the server.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define ONBOARDING_REJECTED_RESPONSE_STATUS_CODE_STRING                           "StatusCode"

/**
 * @brief The key for the error code entry in the "rejected" response payload from the server.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define ONBOARDING_REJECTED_RESPONSE_ERROR_CODE_STRING                            "ErrorCode"

/**
 * @brief The key for the status message entry in the "rejected" response payload from the server.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define ONBOARDING_REJECTED_RESPONSE_ERROR_MESSAGE_STRING                         "ErrorMessage"



/*---------------------- Onboarding internal data structures ----------------------*/

/**
 * @brief Enumerations representing each of the Onboarding library's API functions.
 */
typedef enum _onboardingOperationType
{
    ONBOARDING_GET_DEVICE_CREDENTIALS = 0, /**< @ref onboarding_function_getdevicecredentials */
    ONBOARDING_ONBOARD_DEVICE = 1,         /**< @ref onboarding_function_onboarddevice */
} _onboardingOperationType_t;

/**
 *  @brief Union representing either of the 2 Onboarding operation APIs' callbacks.
 *
 * @note If an ongoing operation was started by the @ref onboarding_function_getdevicecredentials API,
 * then #_onboardingCallbackInfo.getDeviceCredentialsCallback will be valid, whereas if the active
 * operation relates to the @ref AwsIotOnboarding_OnboardDevice API, then
 *#_onboardingCallbackInfo.getDeviceCredentialsCallback will be valid.
 */
typedef union _onboardingCallbackInfo
{
    /* The callback provided by the user to the @ref onboarding_function_getdevicecredentials API. */
    AwsIotOnboardingGetDeviceCredentialsCallbackInfo_t getDeviceCredentialsCallback;

    /* The callback provided by the user to the @ref onboarding_function_onboarddevice API. */
    AwsIotOnboardingOnboardDeviceCallbackInfo_t onboardDeviceCallback;
} _onboardingCallbackInfo_t;

/**
 * @brief Functor for parsing response payload received from Onboarding service.
 * Parser that will de-serialize the server response, allocate memory for representing parsed data (if required),
 * and invoke the user callback passed to it.
 * @param[in] responseType The type of response, "accepted" or "rejected" received from the server for the operation.
 * @param[in] responsePayload The response payload to parse.
 * @param[in] responsePayloadLength The length of the response payload.
 * @param[in] usercallback The user-provided callback to invoke on successful parsing of device credentials.
 */
typedef AwsIotOnboardingError_t ( * _onboardingServerResponseParser)( AwsIotStatus_t responseType,
                                                                      const void * responsePayload,
                                                                      size_t responsePayloadLength,
                                                                      const _onboardingCallbackInfo_t * userCallback );

/**
 * @brief Internal structure representing the data of an Onboarding operation.
 */
typedef struct _onboardingOperationInfo
{
    AwsIotOnboardingError_t status;         /**< @brief Status of operation. */
    _onboardingCallbackInfo_t userCallback; /**< @brief User-provided callback to be called on
                                             * receiving a response from the server.*/
} _onboardingOperationInfo_t;

/**
 * @brief Internal structure representing a single Onboarding operation.
 */
typedef struct _onboardingOperation
{
    IotMutex_t lock;                    /**< @brief Must be acquired before modifying this operation object. */
    uint32_t mutexReferenceCount;       /**< @brief An atomic reference counter for safeguarding mutex access across
                                         * thread contexts. */
    _onboardingOperationInfo_t info;    /**< @brief The Onboarding operation object that is protected by the above
                                         * mutex. */
    IotSemaphore_t responseReceivedSem; /**< @brief Semaphore to be used used by the synchronous API functions @ref
                                         * onboarding_function_getdevicecredentials and @ref
                                         * onboarding_function_onboarddevice. */
} _onboardingOperation_t;

/* TODO - Add documentation! */
extern uint32_t _AwsIotOnboardingMqttTimeoutMs;

/**
 * @brief Pointer to the encoder utility that will be used for serialization
 * of payload data in the library.
 */
extern const IotSerializerEncodeInterface_t * _pAwsIotOnboardingEncoder;

/**
 * @brief Pointer to the decoder utility that will be used for de-serialization
 * of payload data in the library.
 */
extern const IotSerializerDecodeInterface_t * _pAwsIotOnboardingDecoder;

/*---------------------- Onboarding internal functions ----------------------*/

/**
 * @brief Utility for generating the request/response MQTT topic filter string for the OnboardingDevice service API.
 *
 * @param[in] pTemplateIdentifier The template ID string for inserting in the topic filter string.
 * @param[in] templateIdentifierLength The length of the template ID string.
 * @param[out] pTopicFilterBuffer The pre-allocated buffer for storing the generated topic filter.
 * The buffer should have the required minimum size for storing the MQTT topic filter for the OnboardDevice API.
 *
 * @return Returns the size of the generated topic filter.
 */
size_t _AwsIotOnboarding_GenerateOnboardDeviceTopicFilter( const char * pTemplateIdentifier,
                                                           size_t templateIdentifierLength,
                                                           char * pTopicFilterBuffer );

/**
 * @brief Parses the response received from the server for device credentials, and invokes the provided user-callback
 * with parsed credentials, if parsing was successful.
 *
 * @param[in] responseType The type of response, "accepted" or "rejected" received from the server for the operation.
 * @param[in] pDeviceCredentialsResponse The response payload from the server to parse.
 * @param[in] deviceCredentialsResponseLength The length of the response payload.
 * @param[in] userCallback The user-provided callback to invoke on successful parsing of response.
 */
AwsIotOnboardingError_t _AwsIotOnboarding_ParseDeviceCredentialsResponse( AwsIotStatus_t responseType,
                                                                          const void * pDeviceCredentialsResponse,
                                                                          size_t deviceCredentialsResponseLength,
                                                                          const _onboardingCallbackInfo_t * userCallbackInfo );

/**
 * @brief Parses the response payload received from the server for device onboarding, and invokes the provided
 * user-callback with parsed data, if parsing was successful.
 *
 * @param[in] responseType The type of response, "accepted" or "rejected" received from the server for the operation.
 * @param[in] pResponsePayload The response payload from the server to parse.
 * @param[in] responsePayloadLength The length of the response payload.
 * @param[in] userCallbackInfo The user-provided callback to invoke on successful parsing of response.
 */
AwsIotOnboardingError_t _AwsIotOnboarding_ParseOnboardDeviceResponse( AwsIotStatus_t responseType,
                                                                      const void * pResponsePayload,
                                                                      size_t responsePayloadLength,
                                                                      const _onboardingCallbackInfo_t * userCallbackInfo );

/**
 * @brief Serializes for payload of MQTT request to the GetDeviceCredentials service API.
 *
 * @param[in] pOutermostEncoder The encoder object to use for serializing payload.
 * @param[in/out] pSerializationBuffer The pre-allocated buffer for storing the serialized data.
 * @param[in] bufferSize The size of the serialization buffer.
 * @return #AWS_IOT_SERIALIZER_SUCCESS if serialization is successful; otherwise #AWS_IOT_SERIALIZER_BAD_PARAMETER
 * if the device context data cannot be appended to the payload.
 */
AwsIotOnboardingError_t _AwsIotOnboarding_SerializeGetDeviceCredentialsRequestPayload( IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                                       uint8_t * pSerializationBuffer,
                                                                                       size_t bufferSize );

/**
 * @brief Serializes for payload of MQTT request to the OnboardDevice service API.
 *
 * @param[in] pRequestData The data that will be serialized for sending with the request.
 * @param[in] pOutermostEncoder The encoder object to use for serializing payload.
 * @param[in/out] pSerializationBuffer The pre-allocated buffer for storing the serialized data.
 * @param[in] bufferSize The size of the serialization buffer.
 * @return #AWS_IOT_SERIALIZER_SUCCESS if serialization is successful; otherwise #AWS_IOT_SERIALIZER_BAD_PARAMETER
 * if the device context data cannot be appended to the payload.
 */
AwsIotOnboardingError_t _AwsIotOnboarding_SerializeOnboardDeviceRequestPayload( const AwsIotOnboardingOnboardDeviceRequestInfo_t * pRequestData,
                                                                                IotSerializerEncoderObject_t * pOutermostEncoder,
                                                                                uint8_t * pSerializationBuffer,
                                                                                size_t bufferSize );

#endif /* ifndef AWS_IOT_ONBOARDING_INTERNAL_H_ */
