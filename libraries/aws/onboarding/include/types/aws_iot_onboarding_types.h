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
 * @file aws_iot_onboarding_types.h
 * @brief Types of the Onboarding library.
 */

#ifndef AWS_IOT_ONBOARDING_TYPES_H_
#define AWS_IOT_ONBOARDING_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* AWS IoT common header. */
#include "aws_iot.h"

/* Standard includes. */
#include <stdint.h>
#include <stddef.h>

/* Type includes. */
#include "types/iot_platform_types.h"

/*-------------------------- Onboarding enumerated types --------------------------*/

/**
 * @enums{onboarding,onboarding library}
 */

/**
 * @ingroup onboarding_datatypes_enums
 * @brief Return codes of [Onboarding functions](@ref onboarding_functions).
 *
 * The function @ref onboarding_function_strerror can be used to get a return code's
 * description.
 */
typedef enum AwsIotOnboardingError
{
    /**
     * @brief Onboarding operation completed successfully.
     *
     * Functions that may return this value:
     */
    AWS_IOT_ONBOARDING_SUCCESS = 0,

    /**
     * @brief Library initialization failure.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_init
     */
    AWS_IOT_ONBOARDING_INIT_FAILED,

    /**
     * @brief An API function was called before @ref onboarding_function_init.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_NOT_INITIALIZED,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_BAD_PARAMETER,

    /**
     * @brief Onboarding operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_NO_MEMORY,

    /**
     * @brief Onboarding response received from the network is malformed, corrupt or incomplete.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_BAD_RESPONSE,

    /**
     * @brief An Onboarding operation timed out.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_TIMEOUT,

    /**
     * @brief An Onboarding operation request is rejected by the server.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_SERVER_REFUSED,

    /**
     * @brief Onboarding operation failed due to internal error.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_INTERNAL_FAILURE,

    /**
     * @brief Generic code for any MQTT operation error encountered during an
     * Onboarding operation.
     *
     * Functions that may return this value:
     * - @ref onboarding_function_getdevicecredentials
     * - @ref onboarding_function_onboarddevice
     */
    AWS_IOT_ONBOARDING_MQTT_ERROR
} AwsIotOnboardingError_t;

/**
 * @ingroup onboarding_datatypes_enums
 * @brief Status code sent by the server in "rejected" response during an Onboarding operations.
 *
 * These status codes will be sent as parameters to #AwsIotOnboardingGetDeviceCredentialsCallbackInfo_t
 * and #AwsIotOnboardingOnboardDeviceCallbackInfo_t callback functions when the server send a
 * "rejected" response for an operation.
 */
typedef enum AwsIotOnboardingServerStatusCode
{
    /**
     * @brief Onboarding operation rejected: Forbidden.
     */
    AWS_IOT_ONBOARDING_FORBIDDEN = 403,

    /**
     * @brief Onboarding operation rejected: Template ID not found.
     */
    AWS_IOT_ONBOARDING_NOT_FOUND = 404,

    /**
     * @brief Onboarding operation rejected: Server has too many requests from clients.
     */
    AWS_IOT_ONBOARDING_TOO_MANY_REQUESTS = 429,

    /**
     * @brief Onboarding operation rejected due to server internal error.
     */
    AWS_IOT_ONBOARDING_INTERNAL_SERVER_ERROR = 500,
} AwsIotOnboardingServerStatusCode_t;

/*------------------------- Onboarding parameter structs --------------------------*/

/**
 * @paramstructs{onboarding,Onboarding}
 */

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief A key-value string pair representation of an entry in the list of parameters that will be
 * sent as part of the request payload to the server for onboarding the device.
 *
 * @paramfor @ref onboarding_function_onboarddevice
 */
typedef struct AwsIotOnboardingRequestParameterEntry
{
    const char * pParameterKey;   /**< The key string of the parameter entry. */
    size_t parameterKeyLength;    /**< The length of the key string. */
    const char * pParameterValue; /**< The value string of the parameter entry. */
    size_t parameterValueLength;  /**< The length of the value string. */
} AwsIotOnboardingRequestParameterEntry_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief A key-value string pair representation of an entry in the list of device configuration data
 * that is received in the response payload from the server when onboarding the device.
 */
typedef struct AwsIotOnboardingResponseDeviceConfigurationEntry
{
    const char * pKey;   /**< The key string of the device configuration entry. */
    size_t keyLength;    /**< The length of the key string. */
    const char * pValue; /**< The value string of the device configuration entry. */
    size_t valueLength;  /**< The length of the value string. */
} AwsIotOnboardingResponseDeviceConfigurationEntry_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief Aggregates information required for sending a request to the Onboarding service for
 * onboarding a device to its customer AWS IoT account.
 */
typedef struct AwsIotOnboardingOnboardDeviceRequestInfo
{
    /**
     * @brief The identifier of the template on the AWS IoT account used for onboarding the device.
     */
    const char * pTemplateIdentifier;

    /**
     * @brief The length of the template identifier.
     */
    size_t templateIdentifierLength;

    /**
     *  @brief The certificate ID string (of the certificate issued by AWS IoT) to onboard the device with.
     */
    const char * pDeviceCertificateId;

    /**
     * @brief The length of the certificate ID. (Should be 64 characters long)
     */
    size_t deviceCertificateIdLength;

    /**
     * @brief The list of parameter entries to send to the server for onboarding the device.
     */
    const AwsIotOnboardingRequestParameterEntry_t * pParametersStart;

    /**
     * @brief The number of entries in the parameter list.
     */
    size_t numOfParameters;
} AwsIotOnboardingOnboardDeviceRequestInfo_t;

typedef struct AwsIotOnboardingOnboardDeviceAcceptedResponse
{
    /**< The name of the Thing resource that was created to onboard the device.*/
    const char * pThingName;

    /**< The length of the Thing resource name. */
    size_t thingNameLength;

    /**< A list of device configuration data that is received from the server. */
    const AwsIotOnboardingResponseDeviceConfigurationEntry_t * pDeviceConfigList;

    /**< The number of configuration entries in the device configuration list. */
    size_t numOfConfigurationEntries;
} AwsIotOnboardingOnboardDeviceAcceptedResponse_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief Parameter to a Onboarding callback function.
 *
 * @paramfor Onboarding server rejected response callback functions
 *
 * The Onboarding library passes this struct to a callback function whenever an
 * Onboarding operation completes with a rejected response from the server.
 */
typedef struct AwsIotOnboardingRejectedResponse
{
    AwsIotOnboardingServerStatusCode_t statusCode; /**< The highest level HTTP based status code sent by the server. */
    const char * pErrorCode;                       /**< The more granular level error code string sent by the server. */
    size_t errorCodeLength;                        /**< The length of the error code string.*/
    const char * pErrorMessage;                    /**< The most granular level error information is provided in the
                                                    * message by the server. */
    size_t errorMessageLength;                     /**< The length of the error messsage sent by the server. */
} AwsIotOnboardingRejectedResponse_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief Parameter that encapsulates the server response to the callback function for the
 * #AwsIotOnboarding_GetDeviceCredentials API.
 *
 * @paramfor Onboarding server accepted response callback functions
 *
 * The #AwsIotOnboarding_GetDeviceCredentials library API passes this object to a user-provided callback function
 * whenever the operation completes with a response from the server.
 */
typedef struct AwsIotOnboardingGetDeviceCredentialsResponse
{
    /* Represents the status of the operation based on the server response. */
    AwsIotStatus_t operationStatus;

    union
    {
        /* Represents the successful/accepted response of device credentials received from the server. */
        struct
        {
            const char * pDeviceCertificate; /**< The new certificate for the device.*/
            size_t deviceCertificateLength;  /**< The size of the device certificate.*/
            const char * pCertificateId;     /**< The certificate ID associated with the new certificate,
                                              * @p pDeviceCertificate.*/
            size_t certificateIdLength;      /**< The length of the certificate ID.*/
            const char * pPrivateKey;        /**< The private key associated with the new certificate,
                                              * @p pDeviceCertificate.*/
            size_t privateKeyLength;         /**< The size of the private key.*/
        } acceptedResponse;

        /* Represents the rejected response information received from the server. */
        AwsIotOnboardingRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotOnboardingGetDeviceCredentialsResponse_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief User-specific callback information for handling server response for the GetDeviceCredentials service API.
 *
 * @paramfor @ref onboarding_function_getdevicecredentials
 *
 * Provides a function to be invoked on successful completion of an #AwsIotOnboarding_GetDeviceCredentials API
 * operation.
 *
 * @initializer{AwsIotOnboardingCallbackInfo_t,AWS_IOT_ONBOARDING_ACCEPTED_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotOnboardingGetDeviceCredentialsCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotOnboardingGetDeviceCredentialsCallbackInfo.userParam
     * @param[in] AwsIotOnboardingCallbackParam_t* Parsed server response of either device credentials
     * or onboarded device information.
     *
     * @see #AwsIotOnboardingCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         const AwsIotOnboardingGetDeviceCredentialsResponse_t * ); /*<** The user-provided callback to
                                                                                    * invoke; with the
                                                                                    *#AwsIotOnboardingGetDeviceCredentialsCallbackInfo.userParam
                                                                                    * data as the #first parameter. */
} AwsIotOnboardingGetDeviceCredentialsCallbackInfo_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief Parameter that encapsulates the server response to the callback function for the
 * #AwsIotOnboarding_OnboardDevice API.
 *
 * @paramfor Onboarding server accepted response callback functions
 *
 * The #AwsIotOnboarding_OnboardDevice library API passes this object to a user-provided callback function whenever
 * the operation completes with a response from the server.
 */
typedef struct AwsIotOnboardingOnboardDeviceResponse
{
    /* Represents the status of the operation from the server response. */
    AwsIotStatus_t operationStatus;

    union
    {
        /* Represents the successful/accepted response from the server for the request to onboard device. */
        struct
        {
            /**< The name of the Thing resource that was created to onboard the device.*/
            const char * pThingName;

            /**< The length of the Thing resource name. */
            size_t thingNameLength;

            /**< A list of device configuration data that is received from the server. */
            const AwsIotOnboardingResponseDeviceConfigurationEntry_t * pDeviceConfigList;

            /**< The number of configuration entries in the device configuration list. */
            size_t numOfConfigurationEntries;
        } acceptedResponse;

        /* Represents the rejected response information received from the server. */
        AwsIotOnboardingRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotOnboardingOnboardDeviceResponse_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief User-specific callback information for handling server response for the OnboardDevice service API.
 *
 * @paramfor @ref onboarding_function_onboarddevice
 *
 * Provides a function to be invoked on successful completion of an #AwsIotOnboarding_OnboardDevice API
 * operation.
 *
 * @initializer{AwsIotOnboardingOnboardDeviceCallbackInfo_t,AWS_IOT_ONBOARDING_ONBOARD_DEVICE_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotOnboardingOnboardDeviceCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotOnboardingOnboardDeviceCallbackInfo.userParam
     * @param[in] AwsIotOnboardingCallbackParam_t* Parsed server response of either device credentials
     * or onboarded device information.
     *
     * @see #AwsIotOnboardingCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         const AwsIotOnboardingOnboardDeviceResponse_t * ); /*<** The user-provided callback to
                                                                             * invoke; with the
                                                                             *#AwsIotOnboardingOnboardDeviceCallbackInfo.userParam
                                                                             * data as the #first parameter. */
} AwsIotOnboardingOnboardDeviceCallbackInfo_t;

/*------------------------ Onboarding defined constants -------------------------*/

/* @[define_onboarding_initializers] */
#define AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_CALLBACK_INFO_INITIALIZER    { 0 } /**< @brief Initializer for
                                                                                      * #AwsIotOnboardingGetDeviceCredentialsCallbackInfo_t
                                                                                      **/
#define AWS_IOT_ONBOARDING_ONBOARD_DEVICE_CALLBACK_INFO_INITIALIZER            { 0 } /**< @brief Initializer for
                                                                                      * #AwsIotOnboardingOnboardDeviceCallbackInfo_t
                                                                                      **/
/** @brief Initializer for #AwsIotOnboardingOnboardDeviceInfo_t. */
#define AWS_IOT_ONBOARDING_ONBOARD_DEVICE_INFO_INITIALIZER                     { 0 }
/* @[define_onboarding_initializers] */

/**
 * @anchor OnboardingFormat
 * @name Serialization Format
 *
 * @brief Format constants: CBOR
 */
/**@{ */
#define AWS_IOT_ONBOARDING_FORMAT_CBOR    1                                      /**< CBOR format. */
/**@} */

/**
 * @section onboarding_constants_flags Onboarding Function Flags
 * @brief Flags that modify the behavior of Onboarding library functions.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * Onboarding library functions.
 *
 * The following flag is valid for the Onboarding GetDeviceCredentials function:
 * @ref onboarding_function_getdevicecredentials
 * - #AWS_IOT_ONBOARDING_FLAG_ENCRYPT_CREDENTIALS <br>
 *   @copybrief AWS_IOT_ONBOARDING_FLAG_ENCRYPT_CREDENTIALS
 */

/**
 * @brief Flag for requesting encryption of device credentials in server response.
 *
 * @note Set the flags parameter passed to @ref onboarding_function_getdevicecredentials to this
 * value when using to enable credentials encryption in the response from the server.
 */
#define AWS_IOT_ONBOARDING_FLAG_ENCRYPT_CREDENTIALS    0x00000001

#endif /* ifndef AWS_IOT_ONBOARDING_TYPES_H_ */
