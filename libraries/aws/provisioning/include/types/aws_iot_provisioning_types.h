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
    AWS_IOT_PROVISIONING_SUCCESS = 1,

    /**
     * @brief Library initialization failure.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_init
     */
    AWS_IOT_PROVISIONING_INIT_FAILED = 2,

    /**
     * @brief An API function was called before @ref provisioning_function_init.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_NOT_INITIALIZED = 3,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_BAD_PARAMETER = 4,

    /**
     * @brief Provisioning operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_NO_MEMORY = 5,

    /**
     * @brief Provisioning response received from the network is malformed, corrupt or incomplete.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_BAD_RESPONSE = 6,

    /**
     * @brief An Provisioning operation timed out.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_TIMEOUT = 7,

    /**
     * @brief An Provisioning operation request is rejected by the server.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_SERVER_REFUSED = 8,

    /**
     * @brief Provisioning operation failed due to internal error.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_INTERNAL_FAILURE = 9,

    /**
     * @brief Generic code for any MQTT operation error encountered during an
     * Provisioning operation.
     *
     * Functions that may return this value:
     * - @ref provisioning_function_createkeysandcertificate
     * - @ref provisioning_function_createcertificatefromcsr
     * - @ref provisioning_function_registerthing
     */
    AWS_IOT_PROVISIONING_MQTT_ERROR = 10
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
     * @brief Provisioning operation rejected: Invalid Certificate-Signing Request.
     */
    AWS_IOT_PROVISIONING_SERVER_STATUS_INVALID_CSR = 400,

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
 * @paramstructs{provisioning,Provisioning Library}
 */

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief A key-value string pair representation of an entry in the list of parameters that will be
 * sent as part of the request payload to the server for provisioning the device.
 *
 * @paramfor @ref provisioning_function_registerthing
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
 * @brief Aggregates information required for sending a request to the AWS IoT Core service for
 * provisioning a device to its customer AWS IoT account.
 *
 * @paramfor @ref provisioning_function_registerthing
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
     *  @brief The certificate ID string (of the certificate issued by AWS IoT) to provision the device with.
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

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Parameter to a Provisioning callback function.
 *
 * @paramfor Server rejected response callback functions
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
 * @brief Aggregates the data from AWS IoT Core's response to the certificate creation request with a CSR.
 *
 * @paramfor Response Callback function of @ref provisioning_function_createkeysandcertificate
 *
 * The @ref AwsIotProvisioning_CreateKeysAndCertificate library API passes this object to a user-provided callback
 * function
 * whenever the operation completes with a response from the server.
 */
typedef struct AwsIotProvisioningCreateCertFromCsrResponse
{
    /** @brief The highest level HTTP based status code sent by the server. */
    AwsIotProvisioningServerStatusCode_t statusCode;

    union
    {
        /** @brief Represents the successful/accepted response of device credentials received from the server. */
        struct
        {
            const char * pDeviceCert;         /**< The new certificate for the device.*/
            size_t deviceCertLength;          /**< The size of the device certificate.*/
            const char * pCertId;             /**< The certificate ID associated with the new certificate,
                                               * @p pDeviceCertificate.*/
            size_t certIdLength;              /**< The length of the certificate ID.*/
            const char * pCertOwnershipToken; /**< The token that represents ownership of certificate and
                                               * associated private key that the device.*/
            size_t ownershipTokenLength;      /**< The size of the ownership token.*/
        } acceptedResponse;

        /** @brief Represents the rejected response information received from the server. */
        AwsIotProvisioningRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotProvisioningCreateCertFromCsrResponse_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief User-specific callback information for handling server response of the Provisioning CreateCertificateFromCsr
 * service API.
 *
 * @paramfor @ref provisioning_function_registerthing
 *
 * Provides a function that is invoked on completion of an @ref AwsIotProvisioning_CreateCertificateFromCsr API
 * operation.
 *
 * @initializer{AwsIotProvisioningCreateCertFromCsrCallbackInfo_t,AWS_IOT_PROVISIONING_CREATE_CERTIFICATE_FROM_CSR_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotProvisioningCreateCertFromCsrCallbackInfo
{
    void * userParam; /**< The user-provided parameter that is (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] userContext #AwsIotProvisioningCreateCertFromCsrCallbackInfo_t.userParam
     * @param[in] serverResponse Parsed server response of either device credentials
     * or provisioned device information.
     *
     * @see #AwsIotProvisioningCreateCertFromCsrResponse_t for more information on the second parameter.
     */
    void ( * function )( void * userContext,
                         const AwsIotProvisioningCreateCertFromCsrResponse_t * serverResponse ); /*<** The user-provided
                                                                                                  * callback to
                                                                                                  * invoke; with the
                                                                                                  *#AwsIotProvisioningCreateCertFromCsrCallbackInfo.userParam
                                                                                                  * data as the #first
                                                                                                  * parameter. */
} AwsIotProvisioningCreateCertFromCsrCallbackInfo_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Aggregates the data sent as response from AWS IoT Core service for the request to generate new key-pair and
 * certificate for the device.
 *
 * @paramfor Response Callback function of @ref provisioning_function_createkeysandcertificate
 *
 * The @ref AwsIotProvisioning_CreateKeysAndCertificate library API passes this object to a user-provided callback
 * function
 * whenever the operation completes with a response from the server.
 */
typedef struct AwsIotProvisioningCreateKeysAndCertificateResponse
{
    /** @brief The highest level HTTP based status code sent by the server. */
    AwsIotProvisioningServerStatusCode_t statusCode;

    union
    {
        /** @brief Represents the successful/accepted response of device credentials received from the server. */
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

        /** @brief Represents the rejected response information received from the server. */
        AwsIotProvisioningRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotProvisioningCreateKeysAndCertificateResponse_t;


/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief User-specific callback information for handling server response for the Provisioning CreateKeysAndCertificate
 * service API.
 *
 * @paramfor @ref provisioning_function_registerthing
 *
 * Provides a function to be invoked on successful completion of an @ref AwsIotProvisioning_CreateKeysAndCertificate API
 * operation.
 *
 * @initializer{AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t,AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotProvisioningCreateKeysAndCertificateCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] userContext #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t.userParam
     * @param[in] serverResponse Parsed server response of either device credentials
     * or provisioned device information.
     *
     * @see #AwsIotProvisioningCreateKeysAndCertificateResponse_t for more information on the second parameter.
     */
    void ( * function )( void * userContext,
                         const AwsIotProvisioningCreateKeysAndCertificateResponse_t * serverResponse ); /*<** The user-provided
                                                                                                         * callback to
                                                                                                         * invoke; with the
                                                                                                         *#AwsIotProvisioningCreateKeysAndCertificateCallbackInfo.userParam
                                                                                                         * data as the #first
                                                                                                         * parameter. */
} AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief Aggregates the AWS IoT Core server response data sent for the request to provision device.
 *
 * @paramfor Response Callback function of @ref provisioning_function_registerthing
 *
 * The @ref AwsIotProvisioning_RegisterThing library API passes this object as a parameter to a user-provided callback
 * function whenever the operation completes with a response from the server.
 */
typedef struct AwsIotProvisioningRegisterThingResponse
{
    /**< @brief The highest level HTTP based status code sent by the server. */
    AwsIotProvisioningServerStatusCode_t statusCode;

    union
    {
        struct
        {
            /**< @brief The name of the Thing resource that was created to provision the device.*/
            const char * pThingName;

            /**< @brief The length of the Thing resource name. */
            size_t thingNameLength;

            /**< @brief A list of device configuration data that is received from the server. */
            const AwsIotProvisioningResponseDeviceConfigurationEntry_t * pDeviceConfigList;

            /**< @brief The number of configuration entries in the device configuration list. */
            size_t numOfConfigurationEntries;
        } acceptedResponse; /**< @brief Represents the information received as response from the AWS IoT Core service
                             * when the request for provisioning device with the Fleet Provisioning feature is
                             * successful */

        /**< @brief Represents the rejected response information received from the server. */
        AwsIotProvisioningRejectedResponse_t rejectedResponse;
    } u; /**< @brief Valid member depends on operation status. */
} AwsIotProvisioningRegisterThingResponse_t;

/**
 * @ingroup provisioning_datatypes_paramstructs
 * @brief User-specific callback information for handling server response for the Provisioning RegisterThing service
 * API.
 *
 * @paramfor @ref provisioning_function_registerthing
 *
 * Provides a function to be invoked on successful completion of an @ref AwsIotProvisioning_RegisterThing API
 * operation.
 *
 * @initializer{AwsIotProvisioningRegisterThingCallbackInfo_t,AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotProvisioningRegisterThingCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function (optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] userContext #AwsIotProvisioningRegisterThingCallbackInfo_t.userParam
     * @param[in] serverResponse Parsed server response of either device credentials
     * or provisioned device information.
     *
     * @see #AwsIotProvisioningRegisterThingResponse_t for more information on the second parameter.
     */
    void ( * function )( void * userContext,
                         const AwsIotProvisioningRegisterThingResponse_t * serverResponse ); /*<** The user-provided callback to
                                                                                              * invoke; with the
                                                                                              *#AwsIotProvisioningRegisterThingCallbackInfo.userParam
                                                                                              * data as the #first parameter. */
} AwsIotProvisioningRegisterThingCallbackInfo_t;

/*------------------------ Provisioning defined constants -------------------------*/

/* @[define_provisioning_initializers] */
#define AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER    { 0 } /**< @brief Initializer for
                                                                                             * #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t
                                                                                             **/
#define AWS_IOT_PROVISIONING_CREATE_CERTIFICATE_FROM_CSR_CALLBACK_INFO_INITIALIZER    { 0 } /**< @brief Initializer for
                                                                                             * #AwsIotProvisioningCreateCertFromCsrCallbackInfo_t
                                                                                             **/
#define AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER                 { 0 } /**< @brief Initializer for
                                                                                             * #AwsIotProvisioningRegisterThingCallbackInfo_t
                                                                                             **/
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
 * @ref provisioning_function_registerthing
 * - #AWS_IOT_PROVISIONING_FLAG_ENCRYPT_CREDENTIALS <br>
 *   @copybrief AWS_IOT_PROVISIONING_FLAG_ENCRYPT_CREDENTIALS
 */

/**
 * @brief Flag for requesting encryption of device credentials in server response.
 *
 * @note Set the flags parameter passed to @ref provisioning_function_registerthing to this
 * value when using to enable credentials encryption in the response from the server.
 */
#define AWS_IOT_PROVISIONING_FLAG_ENCRYPT_CREDENTIALS    0x00000001

#endif /* ifndef AWS_IOT_PROVISIONING_TYPES_H_ */
