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
 * @file aws_iot_provisioning_internal.h
 * @brief Internal header of Provisioning library. This header should not be included in
 * typical application code.
 */

#ifndef AWS_IOT_PROVISIONING_INTERNAL_H_
#define AWS_IOT_PROVISIONING_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* AWS IoT common header include. */
#include "aws_iot.h"

/* Provisioning include. */
#include "aws_iot_provisioning.h"

/* Serializer include. */
#include "iot_serializer.h"

/**
 * @def AwsIotProvisioning_Assert( expression )
 * @brief Assertion macro for the Provisioning library.
 *
 * Set @ref AWS_IOT_PROVISIONING_ENABLE_ASSERTS to `1` to enable assertions in the Provisioning
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if AWS_IOT_PROVISIONING_ENABLE_ASSERTS == 1
    #ifndef AwsIotProvisioning_Assert
        #ifdef Iot_DefaultAssert
            #define AwsIotProvisioning_Assert( expression )    Iot_DefaultAssert( expression )
        #else
            #error "Asserts are enabled for MQTT, but AwsIotProvisioning_Assert is not defined"
        #endif
    #endif
#else
    #define AwsIotProvisioning_Assert( expression )
#endif

/* Configure logs for PROVISIONING functions. */
#ifdef AWS_IOT_LOG_LEVEL_PROVISIONING
    #define LIBRARY_LOG_LEVEL        AWS_IOT_LOG_LEVEL_PROVISIONING
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "Provisioning" )
#include "iot_logging_setup.h"

/**
 * @brief Printable names for each of the Provisioning operations.
 */
/**@{ */
#define CREATE_KEYS_AND_CERTIFICATE_OPERATION_LOG    "GET DEVICE CREDENTIALS"
#define REGISTER_THING_OPERATION_LOG                 "PROVISION DEVICE"
/**@} */

/**
 * @brief Default format for communication payload with AWS IoT Core service for Fleet Provisioning feature.
 *
 * <b>Possible values:</b>  #AWS_IOT_PROVISIONING_FORMAT_CBOR (JSON is not supported for now by the library) <br>
 * <b>Recommended values:</b> Cbor is more compact than Json, thus more efficient. <br>
 * <b>Default value (if undefined):</b>  #AWS_IOT_PROVISIONING_FORMAT_CBOR <br>
 */
#ifndef AWS_IOT_PROVISIONING_FORMAT
    #define AWS_IOT_PROVISIONING_FORMAT    AWS_IOT_PROVISIONING_FORMAT_CBOR
#endif

/* In current release, JSON format is not supported. */
#if AWS_IOT_PROVISIONING_FORMAT == AWS_IOT_PROVISIONING_FORMAT_JSON
    #error "AWS_IOT_PROVISIONING_FORMAT_JSON is not supported."
#endif

/**
 * Define encoder/decoder based on configuration AWS_IOT_PROVISIONING_FORMAT.
 */
#if AWS_IOT_PROVISIONING_FORMAT == AWS_IOT_PROVISIONING_FORMAT_CBOR
    #define PROVISIONING_FORMAT    "cbor"
#else /* if AWS_IOT_PROVISIONING_FORMAT == AWS_IOT_PROVISIONING_FORMAT_CBOR */
    #error "AWS_IOT_PROVISIONING_FORMAT must be AWS_IOT_PROVISIONING_FORMAT_CBOR."
#endif /* if AWS_IOT_PROVISIONING_FORMAT == AWS_IOT_PROVISIONING_FORMAT_CBOR */

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "iot_static_memory.h"

/**
 * @brief Allocate buffer for the payload of an MQTT publish operation. This function should have the same
 * signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotProvisioning_MallocPayload    Iot_MallocMessageBuffer

/**
 * @brief Free an MQTT publish payload buffer. This function should have the same
 * signature as [free](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotProvisioning_FreePayload      Iot_FreeMessageBuffer

/**
 * @brief Allocate a buffer for a short string, which is used for temporarily storing the
 * "parameter" name during serialization of the publish payload of a registerthing
 * request operation. This function should have the same signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotProvisioning_MallocString     Iot_MallocMessageBuffer

/**
 * @brief Free a string. This function should have the same
 * signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotProvisioning_FreeString       Iot_FreeMessageBuffer


/**
 * @brief Allocate a list of #AwsIotProvisioningResponseDeviceConfigurationEntry_t.
 * This function should have the same signature as [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define AwsIotProvisioning_MallocDeviceConfigurationList    Iot_MallocMessageBuffer

/**
 * @brief Free a list of #AwsIotProvisioningResponseDeviceConfigurationEntry_t.
 * This function should have the same signature as [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define AwsIotProvisioning_FreeDeviceConfigurationList      Iot_FreeMessageBuffer


#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #ifndef AwsIotProvisioning_MallocPayload
        #ifdef Iot_DefaultMalloc
            #define AwsIotProvisioning_MallocPayload    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for AwsIotProvisioning_MallocPayload"
        #endif
    #endif

    #ifndef AwsIotProvisioning_FreePayload
        #ifdef Iot_DefaultFree
            #define AwsIotProvisioning_FreePayload    Iot_DefaultFree
        #else
            #error "No Free function defined for AwsIotProvisioning_FreePayload"
        #endif
    #endif

    #ifndef AwsIotProvisioning_MallocString
        #ifdef Iot_DefaultMalloc
            #define AwsIotProvisioning_MallocString    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for AwsIotProvisioning_MallocString"
        #endif
    #endif

    #ifndef AwsIotProvisioning_FreeString
        #ifdef Iot_DefaultFree
            #define AwsIotProvisioning_FreeString    Iot_DefaultFree
        #else
            #error "No Free function defined for AwsIotProvisioning_FreeString"
        #endif
    #endif

    #ifndef AwsIotProvisioning_MallocDeviceConfigurationList
        #ifdef Iot_DefaultMalloc
            #define AwsIotProvisioning_MallocDeviceConfigurationList    Iot_DefaultMalloc
        #else
            #error "No malloc function defined for AwsIotProvisioning_MallocDeviceConfigurationList"
        #endif
    #endif

    #ifndef AwsIotProvisioning_FreeDeviceConfigurationList
        #ifdef Iot_DefaultFree
            #define AwsIotProvisioning_FreeDeviceConfigurationList    Iot_DefaultFree
        #else
            #error "No Free function defined for AwsIotProvisioning_FreeDeviceConfigurationList"
        #endif
    #endif

#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS
    #define AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS    ( 5000 )
#endif
/** @endcond */

/**
 * @brief The MQTT response topic filter for the Provisioning CreateKeysAndCertificate service API.
 *
 * @note The complete response topics are suffixed with `AWS_IOT_ACCEPTED_SUFFIX` or `AWS_IOT_REJECTED_SUFFIX` strings.
 * It should be utilized in the @ref provisioning_function_registerthing API function.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER \
    "$aws/certificates/create/"PROVISIONING_FORMAT

/**
 * @brief Length of the MQTT response topic filter for the Provisioning CreateKeysAndCertificate service API.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER_LENGTH \
    ( ( uint16_t ) ( sizeof( PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER ) - 1 ) )

/**
 * @brief The length of the longest MQTT response topic of the Provisioning CreateKeysAndCertificate service API.
 * Out of the two response topics, the "rejected" has the longest length.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_MAX_TOPIC_LENGTH \
    ( PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER_LENGTH + sizeof( AWS_IOT_REJECTED_SUFFIX ) )

/**
 * @brief The MQTT request topic for the Provisioning CreateKeysAndCertificate service API.
 *
 * @note It should be utilized in the @ref provisioning_function_registerthing API function.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC \
    "$aws/certificates/create/"PROVISIONING_FORMAT

/**
 * @brief The length of the MQTT request topic for the Provisioning CreateKeysAndCertificate service API.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC_LENGTH \
    ( ( uint16_t ) ( sizeof( PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_REQUEST_TOPIC ) - 1 ) )

/**
 * @brief The key for the device certificate entry in the response payload of the Provisioning CreateKeysAndCertificate
 * service API.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING          "certificatePem"

/**
 * @brief The key for the certificate Id entry in the response payload of the Provisioning CreateKeysAndCertificate
 * service API.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING           "certificateId"

/**
 * @brief The key for the private key entry in the response payload of the Provisioning CreateKeysAndCertificate service
 * API.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING              "privateKey"

/**
 * @brief The key for the token key entry in the response payload of the Provisioning CreateKeysAndCertificate service
 * API.
 */
#define PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_PAYLOAD_CERTIFICATE_TOKEN_KEY_STRING    "certificateOwnershipToken"

/**
 * @brief The common path in the request and response MQTT topics of the Provisioning RegisterThing service API.
 */
#define PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX \
    "$aws/provisioning-templates/"

/**
 * @brief The length of the common path in the request and response MQTT topics of the Provisioning RegisterThing
 * service API.
 */
#define PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX_LENGTH \
    ( ( uint16_t ) ( sizeof( PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX ) - 1 ) )

/**
 * @brief The maximum length of the Template name that can be used for provisioning the device.
 * @note The template name is part of the MQTT topics of the Provisioning RegisterThing service API.
 */
#define PROVISIONING_MAX_TEMPLATE_NAME_LENGTH               ( 36 )

/**
 * @brief The common suffix in the request and response MQTT topics of the Provisioning RegisterThing service API.
 */
#define PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX    "/provision/"PROVISIONING_FORMAT

/**
 * @brief The length of the common suffix in the MQTT topics of the Provisioning RegisterThing service API.
 */
#define PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX_LENGTH \
    ( ( uint16_t ) ( sizeof( PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX ) - 1 ) )


/**
 * @brief The length of the complete MQTT request topic of the Provisioning RegisterThing service API.
 */
#define PROVISIONING_REGISTER_THING_REQUEST_TOPIC_LENGTH                                                \
    ( PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX_LENGTH + PROVISIONING_MAX_TEMPLATE_NAME_LENGTH + \
      PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX_LENGTH )

/**
 * @brief The key for the certificate ID's entry to be inserted in the request payload for the Provisioning
 * RegisterThing service
 * API.
 *
 * @note This should be used in serializing the request payload for sending to the server.
 */
#define PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_CERTIFICATE_ID_STRING       "certificateId"

/**
 * @brief The key for the certificate ownership token's entry to be inserted in the request payload for the
 * provisioning the device.
 *
 * @note This should be used in serializing the request payload for sending to the server.
 */
#define PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_CERTIFICATE_TOKEN_STRING    "certificateOwnershipToken"

/**
 * @brief The key for the device context data's entry to be inserted in the request payload for the RegisterThing
 * service API.
 *
 * @note This should be used in serializing the request payload for sending to the server, only if the calling
 * application provides valid device context data.
 */
#define PROVISIONING_REGISTER_THING_REQUEST_PAYLOAD_PARAMETERS_STRING           "parameters"

/**
 * @brief The length of the MQTT request topic filter of the Provisioning RegisterThing service API.
 */
#define PROVISIONING_REGISTER_THING_RESPONSE_TOPIC_FILTER_LENGTH                                        \
    ( PROVISIONING_REGISTER_THING_TOPICS_COMMON_PREFIX_LENGTH + PROVISIONING_MAX_TEMPLATE_NAME_LENGTH + \
      PROVISIONING_REGISTER_THING_TOPICS_COMMON_SUFFIX_LENGTH )

/**
 * @brief The length of the longest MQTT response topic of the Provisioning RegisterThing service API.
 * Out of the two response topics, the "rejected" has the longest length.
 */
#define PROVISIONING_REGISTER_THING_RESPONSE_MAX_TOPIC_LENGTH \
    ( PROVISIONING_REGISTER_THING_RESPONSE_TOPIC_FILTER_LENGTH + sizeof( AWS_IOT_REJECTED_SUFFIX ) )

/**
 * @brief The key for the device configuration data's entry in the response payload of the Provisioning RegisterThing
 * service API.
 *
 * @note This should be utilized in parsing the success case response payload received from the server.
 */
#define PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_DEVICE_CONFIGURATION_STRING    "deviceConfiguration"

/**
 * @brief The key for the Thing resource name's entry in the response payload of the Provisioning RegisterThing service
 * API.
 *
 * @note This should be utilized in parsing the success case response payload received from the server.
 */
#define PROVISIONING_REGISTER_THING_RESPONSE_PAYLOAD_THING_NAME_STRING              "thingName"

/**
 * @brief The key for the status code entry in the "rejected" response payload from the server.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define PROVISIONING_REJECTED_RESPONSE_STATUS_CODE_STRING                           "statusCode"

/**
 * @brief The key for the error code entry in the "rejected" response payload from the server.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define PROVISIONING_REJECTED_RESPONSE_ERROR_CODE_STRING                            "errorCode"

/**
 * @brief The key for the status message entry in the "rejected" response payload from the server.
 *
 * @note This should be utilized in parsing the response payload received from the server.
 */
#define PROVISIONING_REJECTED_RESPONSE_ERROR_MESSAGE_STRING                         "errorMessage"

/*---------------------- Provisioning internal data structures ----------------------*/

/**
 * @brief Enumerations representing each of the Provisioning library's API functions.
 */
typedef enum _provisioningOperationType
{
    PROVISIONING_CREATE_KEYS_AND_CERTIFICATE = 0, /**< @ref provisioning_function_registerthing */
    PROVISIONING_REGISTER_THING = 1,              /**< @ref provisioning_function_registerthing */
} _provisioningOperationType_t;

/**
 * @brief Union representing either of the 2 Provisioning operation APIs' callbacks.
 *
 * @note If an ongoing operation was started by the @ref provisioning_function_registerthing API,
 * then #_provisioningCallbackInfo_t.createKeysAndCertificateCallback will be valid, whereas if the active
 * operation relates to the @ref AwsIotProvisioning_RegisterThing API, then
 * #_provisioningCallbackInfo_t.registerThingCallback will be valid.
 */
typedef union _provisioningCallbackInfo
{
    /** @brief The callback provided by the user to the @ref provisioning_function_registerthing API. */
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t createKeysAndCertificateCallback;

    /** @brief The callback provided by the user to the @ref provisioning_function_registerthing API. */
    AwsIotProvisioningRegisterThingCallbackInfo_t registerThingCallback;
} _provisioningCallbackInfo_t;

/**
 * @brief Functor for parsing response payload received from AWS IoT Core.
 * Parser that will de-serialize the server response, allocate memory for representing parsed data (if required),
 * and invoke the user callback passed to it.
 * @param[in] responseType The type of response, "accepted" or "rejected" received from the server for the operation.
 * @param[in] responsePayload The response payload to parse.
 * @param[in] responsePayloadLength The length of the response payload.
 * @param[in] usercallback The user-provided callback to invoke on successful parsing of device credentials.
 */
typedef AwsIotProvisioningError_t ( * _provisioningServerResponseParser)( AwsIotStatus_t responseType,
                                                                          const void * responsePayload,
                                                                          size_t responsePayloadLength,
                                                                          const _provisioningCallbackInfo_t * userCallback );

/**
 * @brief Internal structure representing the data of an Provisioning operation.
 */
typedef struct _provisioningOperationInfo
{
    AwsIotProvisioningError_t status;         /**< @brief Status of operation. */
    _provisioningCallbackInfo_t userCallback; /**< @brief User-provided callback to be called on
                                               * receiving a response from the server.*/
} _provisioningOperationInfo_t;

/**
 * @brief Internal structure representing a single Provisioning operation.
 */
typedef struct _provisioningOperation
{
    _provisioningOperationInfo_t info;  /**< @brief The Provisioning operation object. */
    IotSemaphore_t responseReceivedSem; /**< @brief Semaphore to be used used by the synchronous API functions @ref
                                         * provisioning_function_registerthing and @ref
                                         * provisioning_function_registerthing. */
} _provisioningOperation_t;

/*----------------- Declaration of INTERNAL global variables --------------------*/

extern uint32_t _AwsIotProvisioningMqttTimeoutMs;
extern const IotSerializerEncodeInterface_t * _pAwsIotProvisioningEncoder;
extern const IotSerializerDecodeInterface_t * _pAwsIotProvisioningDecoder;

/*---------------------- Declaration of Provisioning INTERNAL functions ----------------------*/

/**
 * @brief Utility for generating the request/response MQTT topic filter string for the ProvisioningDevice service API.
 *
 * @param[in] pTemplateName The template ID string for inserting in the topic filter string.
 * @param[in] templateNameLength The length of the template ID string.
 * @param[out] pTopicFilterBuffer The pre-allocated buffer for storing the generated topic filter.
 * The buffer should have the required minimum size for storing the MQTT topic filter for the Provisioning RegisterThing
 * API.
 *
 * @return Returns the size of the generated topic filter.
 */
size_t _AwsIotProvisioning_GenerateRegisterThingTopicFilter( const char * pTemplateName,
                                                             size_t templateNameLength,
                                                             char * pTopicFilterBuffer );

/**
 * @brief Parses the response received from the server for device credentials, and invokes the provided user-callback
 * with parsed credentials, if parsing was successful.
 *
 * @param[in] responseType The type of response, "accepted" or "rejected" received from the server for the operation.
 * @param[in] pKeysAndCertificateResponse The response payload from the server to parse.
 * @param[in] keysAndCertificateResponseLength The length of the response payload.
 * @param[in] userCallbackInfo The user-provided callback to invoke on successful parsing of response.
 */
AwsIotProvisioningError_t _AwsIotProvisioning_ParseKeysAndCertificateResponse( AwsIotStatus_t responseType,
                                                                               const void * pKeysAndCertificateResponse,
                                                                               size_t keysAndCertificateResponseLength,
                                                                               const _provisioningCallbackInfo_t * userCallbackInfo );

/**
 * @brief Parses the response payload received from the server for device provisioning, and invokes the provided
 * user-callback with parsed data, if parsing was successful.
 *
 * @param[in] responseType The type of response, "accepted" or "rejected" received from the server for the operation.
 * @param[in] pResponsePayload The response payload from the server to parse.
 * @param[in] responsePayloadLength The length of the response payload.
 * @param[in] userCallbackInfo The user-provided callback to invoke on successful parsing of response.
 */
AwsIotProvisioningError_t _AwsIotProvisioning_ParseRegisterThingResponse( AwsIotStatus_t responseType,
                                                                          const void * pResponsePayload,
                                                                          size_t responsePayloadLength,
                                                                          const _provisioningCallbackInfo_t * userCallbackInfo );

/**
 * @brief Serializes payload data for MQTT request to the Provisioning CreateKeysAndCertificate service API.
 *
 * @param[out] pSerializationBuffer This will be assigned to a buffer that will be allocated and populated with the
 * serialized payload data.
 * @param[out] pBufferSize This will be populated with the size of the allocated payload data buffer.
 * @return #AWS_IOT_PROVISIONING_SUCCESS if serialization is successful; otherwise* #AWS_IOT_PROVISIONING_INTERNAL_FAILURE
 * for any serialization error.
 */
AwsIotProvisioningError_t _AwsIotProvisioning_SerializeCreateKeysAndCertificateRequestPayload( uint8_t ** pSerializationBuffer,
                                                                                               size_t * pBufferSize );

/**
 * @brief Serializes payload data for MQTT request to the Provisioning RegisterThing service API.
 *
 * @param[in] pRequestData The data that will be serialized for sending with the request.
 * @param[out] pSerializationBuffer This will be assigned to a buffer that will be allocated and populated with the
 * serialized payload data.
 *
 * @note The calling code is responsible for de-allocation of the buffer memory.
 * @param[out] pBufferSize This will be populated with the size of the allocated payload data buffer.
 * @return #AWS_IOT_PROVISIONING_SUCCESS if serialization is successful; otherwise #AWS_IOT_PROVISIONING_INTERNAL_FAILURE
 * for any serialization error.
 */
AwsIotProvisioningError_t _AwsIotProvisioning_SerializeRegisterThingRequestPayload( const AwsIotProvisioningRegisterThingRequestInfo_t * pRequestData,
                                                                                    uint8_t ** pSerializationBuffer,
                                                                                    size_t * pBufferSize );

#endif /* ifndef AWS_IOT_PROVISIONING_INTERNAL_H_ */
