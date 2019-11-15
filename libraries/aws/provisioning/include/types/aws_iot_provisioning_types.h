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
 * @file aws_iot_provisioning_types.h
 * @brief Types of the Provisioning library.
 */

#ifndef AWS_IOT_PROVISIONING_TYPES_H_
#define AWS_IOT_PROVISIONING_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdint.h>
#include <stddef.h>

/* Type includes. */
#include "types/iot_platform_types.h"

/*-------------------------- Provisioning enumerated types --------------------------*/

/**
 * @enums{provisioning,provisioning library}
 */

/**
 * @ingroup provisioning_datatypes_enums
 * @brief Return codes of [Provisioning functions](@ref provisioning_functions).
 *
 * The function @ref provisioning_function_strerror can be used to get a return code's
 * description.
 */
typedef enum AwsIotProvisioningError
{
    /**
     * @brief Provisioning operation completed successfully.
     *
     * Functions that may return this value:
     */
    AWS_IOT_PROVISIONING_SUCCESS = 0,

    /**
     * @brief Library initialization failure.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_init
     */
    AWS_IOT_PROVISIONING_INIT_FAILED,

    /**
     * @brief An API function was called before @ref provisioning_function_init.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_NOT_INITIALIZED,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_BAD_PARAMETER,

    /**
     * @brief Provisioning operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_NO_MEMORY,

    /**
     * @brief Provisioning response received from the network is malformed, corrupt or incomplete.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_BAD_RESPONSE,

    /**
     * @brief An Provisioning operation timed out.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_TIMEOUT,

    /**
     * @brief An Provisioning operation request is rejected by the server.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_SERVER_REFUSED,

    /**
     * @brief Provisioning operation failed due to internal error.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_INTERNAL_FAILURE,

    /**
     * @brief Generic code for any MQTT operation error encountered during an
     * Provisioning operation.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_getdevicecredentials
     * - @ref provisioning_function_onboarddevice
     */
    AWS_IOT_PROVISIONING_MQTT_ERROR
} AwsIotProvisioningError_t;

/**
 * @ingroup provisioning_datatypes_enums
 * @brief Status code sent by the server in its response during an Provisioning operations.
 *
 * These status codes will be sent as parameters to #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t
 * and #AwsIotProvisioningRegisterThingCallbackInfo_t callback functions on receiving a response from
 * the server.
 */
typedef enum AwsIotProvisioningServerStatusCode
{
    AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED = 202,

    /**
     * @brief Provisioning operation rejected: Forbidden.
     */
    AWS_IOT_PROVISIONING_SERVER_STATUS_FORBIDDEN = 403,

    /**
     * @brief Provisioning operation rejected: Template ID not found.
     */
    AWS_IOT_PROVISIONING_SERVER_STATUS_NOT_FOUND = 404,

    /**
     * @brief Provisioning operation rejected: Server has too many requests from clients.
     */
    AWS_IOT_PROVISIONING_SERVER_STATUS_TOO_MANY_REQUESTS = 429,

    /**
     * @brief Provisioning operation rejected due to server internal error.
     */
    AWS_IOT_PROVISIONING_SERVER_STATUS_INTERNAL_SERVER_ERROR = 500,
} AwsIotProvisioningServerStatusCode_t;

/*------------------------- Provisioning parameter structs --------------------------*/

/**
 * @paramstructs{provisioning,Provisioning}
 */

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief A key-value string pair representation of an entry in the list of parameters that will be
 * sent as part of the request payload to the server for provisioning the device.
 *
 * @paramfor @ref provisioning_function_onboarddevice
 */
typedef struct AwsIotProvisioningRequestParameterEntry
{
    const char * pParameterKey;   /**< The key string of the parameter entry. */
    size_t parameterKeyLength;    /**< The length of the key string. */
    const char * pParameterValue; /**< The value string of the parameter entry. */
    size_t parameterValueLength;  /**< The length of the value string. */
} AwsIotProvisioningRequestParameterEntry_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief A key-value string pair representation of an entry in the list of device configuration data
 * that is received in the response payload from the server when provisioning the device.
 */
typedef struct AwsIotProvisioningResponseDeviceConfigurationEntry
{
    const char * pKey;   /**< The key string of the device configuration entry. */
    size_t keyLength;    /**< The length of the key string. */
    const char * pValue; /**< The value string of the device configuration entry. */
    size_t valueLength;  /**< The length of the value string. */
} AwsIotProvisioningResponseDeviceConfigurationEntry_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Aggregates information required for sending a request to the Provisioning service for
 * provisioning a device to its customer AWS IoT account.
 */
typedef struct AwsIotProvisioningRegisterThingRequestInfo
{
    /**
     * @brief The name of the template on the AWS IoT account to be used for provisioning the device.
     */
    const char * pTemplateName;

    /**
     * @brief The length of the template name text.
     */
    size_t templateNameLength;

    /**
     *  @brief The certificate ID string (of the certificate issued by AWS IoT) to onboard the device with.
     */
    const char * pDeviceCertificateId;

    /**
     * @brief The length of the certificate ID. (Should be 64 characters long)
     */
    size_t deviceCertificateIdLength;

    /**
     * @brief The ownership token for the certificate being requested for provisioning the device with.
     * This token should have been issued by AWS IoT for the same certificate ID being passed.
     */
    const char * pCertificateOwnershipToken;

    /**
     * @brief The length of the ownership token string.
     */
    size_t ownershipTokenLength;

    /**
     * @brief The list of parameter entries to send to the server for provisioning the device.
     */
    const AwsIotProvisioningRequestParameterEntry_t * pParametersStart;

    /**
     * @brief The number of entries in the parameter list.
     */
    size_t numOfParameters;
} AwsIotProvisioningRegisterThingRequestInfo_t;

typedef struct AwsIotProvisioningRegisterThingAcceptedResponse
{
    /**< The name of the Thing resource that was created to onboard the device.*/
    const char * pThingName;

    /**< The length of the Thing resource name. */
    size_t thingNameLength;

    /**< A list of device configuration data that is received from the server. */
    const AwsIotProvisioningResponseDeviceConfigurationEntry_t * pDeviceConfigList;

    /**< The number of configuration entries in the device configuration list. */
    size_t numOfConfigurationEntries;
} AwsIotProvisioningRegisterThingAcceptedResponse_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Parameter to a Provisioning callback function.
 *
 * @paramfor Provisioning server rejected response callback functions
 *
 * The Provisioning library passes this struct to a callback function whenever an
 * Provisioning operation completes with a rejected response from the server.
 */
typedef struct AwsIotProvisioningRejectedResponse
{
    const char * pErrorCode;    /**< The more granular level error code string sent by the server. */
    size_t errorCodeLength;     /**< The length of the error code string.*/
    const char * pErrorMessage; /**< The most granular level error information is provided in the
                                 * message by the server. */
    size_t errorMessageLength;  /**< The length of the error messsage sent by the server. */
} AwsIotProvisioningRejectedResponse_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Encapsulates the server response data sent for the request to generate new key-pair and
 * certificate for the device.
 *
 * @paramfor Provisioning server accepted response callback functions
 *
 * The #AwsIotProvisioning_CreateKeysAndCertificate library API passes this object to a user-provided callback function
 * whenever the operation completes with a response from the server.
 */
typedef struct AwsIotProvisioningCreateKeysAndCertificateResponse
{
    /* The highest level HTTP based status code sent by the server. */
    AwsIotProvisioningServerStatusCode_t statusCode;

    union
    {
        /* Represents the successful/accepted response of device credentials received from the server. */
        struct
        {
            const char * pDeviceCertificate;         /**< The new certificate for the device.*/
            size_t deviceCertificateLength;          /**< The size of the device certificate.*/
            const char * pCertificateId;             /**< The certificate ID associated with the new certificate,
                                                      * @p pDeviceCertificate.*/
            size_t certificateIdLength;              /**< The length of the certificate ID.*/
            const char * pPrivateKey;                /**< The private key associated with the new certificate,
                                                      * @p pDeviceCertificate.*/
            size_t privateKeyLength;                 /**< The size of the private key.*/
            const char * pCertificateOwnershipToken; /**< The token that represents ownership of certificate and
                                                      * associated private key that the device.*/
            size_t ownershipTokenLength;             /**< The size of the ownership token.*/
        } acceptedResponse;

        /* Represents the rejected response information received from the server. */
        AwsIotProvisioningRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotProvisioningCreateKeysAndCertificateResponse_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief User-specific callback information for handling server response for the Provisioning CreateKeysAndCertificate
 * service API.
 *
 * @paramfor @ref provisioning_function_getdevicecredentials
 *
 * Provides a function to be invoked on successful completion of an #AwsIotProvisioning_CreateKeysAndCertificate API
 * operation.
 *
 * @initializer{AwsIotProvisioningCallbackInfo_t,AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotProvisioningCreateKeysAndCertificateCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo.userParam
     * @param[in] AwsIotProvisioningCallbackParam_t* Parsed server response of either device credentials
     * or onboarded device information.
     *
     * @see #AwsIotProvisioningCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         const AwsIotProvisioningCreateKeysAndCertificateResponse_t * ); /*<** The user-provided
                                                                                          * callback to
                                                                                          * invoke; with the
                                                                                          *#AwsIotProvisioningCreateKeysAndCertificateCallbackInfo.userParam
                                                                                          * data as the #first
                                                                                          * parameter. */
} AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Encpasulates the server response data sent for the request to provision device with an AWS IoT issued
 * certificate.
 *
 * @paramfor Provisioning server accepted response callback functions
 *
 * The #AwsIotProvisioning_RegisterThing library API passes this object as a parameter to a user-provided callback
 * function whenever the operation completes with a response from the server.
 */
typedef struct AwsIotProvisioningRegisterThingResponse
{
    /* The highest level HTTP based status code sent by the server. */
    AwsIotProvisioningServerStatusCode_t statusCode;

    union
    {
        /* Represents the successful/accepted response from the server for the request to onboard device. */
        struct
        {
            /**< The name of the Thing resource that was created to onboard the device.*/
            const char * pThingName;

            /**< The length of the Thing resource name. */
            size_t thingNameLength;

            /**< The client ID used in the connection to the AWS IoT server for provisioning the device.*/
            const char * pClientId;

            /**< The length of the client ID text. */
            size_t clientIdLength;

            /**< A list of device configuration data that is received from the server. */
            const AwsIotProvisioningResponseDeviceConfigurationEntry_t * pDeviceConfigList;

            /**< The number of configuration entries in the device configuration list. */
            size_t numOfConfigurationEntries;
        } acceptedResponse;

        /* Represents the rejected response information received from the server. */
        AwsIotProvisioningRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotProvisioningRegisterThingResponse_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief User-specific callback information for handling server response for the Provisioning RegisterThing service
 * API.
 *
 * @paramfor @ref provisioning_function_onboarddevice
 *
 * Provides a function to be invoked on successful completion of an #AwsIotProvisioning_RegisterThing API
 * operation.
 *
 * @initializer{AwsIotProvisioningRegisterThingCallbackInfo_t,AWS_IOT_PROVISIONING_ONBOARD_DEVICE_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotProvisioningRegisterThingCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotProvisioningRegisterThingCallbackInfo.userParam
     * @param[in] AwsIotProvisioningCallbackParam_t* Parsed server response of either device credentials
     * or onboarded device information.
     *
     * @see #AwsIotProvisioningCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         const AwsIotProvisioningRegisterThingResponse_t * ); /*<** The user-provided callback to
                                                                               * invoke; with the
                                                                               *#AwsIotProvisioningRegisterThingCallbackInfo.userParam
                                                                               * data as the #first parameter. */
} AwsIotProvisioningRegisterThingCallbackInfo_t;

/*------------------------ Provisioning defined constants -------------------------*/

/* @[define_provisioning_initializers] */
#define AWS_IOT_PROVISIONING_GET_DEVICE_CREDENTIALS_CALLBACK_INFO_INITIALIZER    { 0 } /**< @brief Initializer for
                                                                                        * #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t
                                                                                        **/
#define AWS_IOT_PROVISIONING_ONBOARD_DEVICE_CALLBACK_INFO_INITIALIZER            { 0 } /**< @brief Initializer for
                                                                                        * #AwsIotProvisioningRegisterThingCallbackInfo_t
                                                                                        **/
/** @brief Initializer for #AwsIotProvisioningRegisterThingInfo_t. */
#define AWS_IOT_PROVISIONING_ONBOARD_DEVICE_INFO_INITIALIZER                     { 0 }
/* @[define_provisioning_initializers] */

/**
 * @anchor ProvisioningFormat
 * @name Serialization Format
 *
 * @brief Format constants: CBOR
 */
/**@{ */
#define AWS_IOT_PROVISIONING_FORMAT_CBOR    1                                      /**< CBOR format. */
/**@} */

/**
 * @section provisioning_constants_flags Provisioning Function Flags
 * @brief Flags that modify the behavior of Provisioning library functions.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * Provisioning library functions.
 *
 * The following flag is valid for the Provisioning CreateKeysAndCertificate function:
 * @ref provisioning_function_getdevicecredentials
 * - #AWS_IOT_PROVISIONING_FLAG_ENCRYPT_CREDENTIALS <br>
 *   @copybrief AWS_IOT_PROVISIONING_FLAG_ENCRYPT_CREDENTIALS
 */

/**
 * @brief Flag for requesting encryption of device credentials in server response.
 *
 * @note Set the flags parameter passed to @ref provisioning_function_getdevicecredentials to this
 * value when using to enable credentials encryption in the response from the server.
 */
#define AWS_IOT_PROVISIONING_FLAG_ENCRYPT_CREDENTIALS    0x00000001

#endif /* ifndef AWS_IOT_PROVISIONING_TYPES_H_ */
