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
 * @brief Types of Onboarding library callbacks.
 *
 * One of these values will be placed in #AwsIotOnboardingCallbackParam_t.callbackType
 * to identify the reason for invoking a callback function.
 */
typedef enum AwsIotOnboardingCallbackType
{
    AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE, /**< Callback invoked because a [Onboarding get device
                                                         * credentials](@ref onboarding_function_delete) completed. */
    AWS_IOT_ONBOARDING_ONBOARD_DEVICE_COMPLETE          /**< Callback invoked because a [Onboarding onboard device](@ref
                                                         * onboarding_function_get) completed. */
} AwsIotOnboardingCallbackType_t;

/*------------------------- Onboarding parameter structs --------------------------*/

/**
 * @paramstructs{onboarding,Onboarding}
 */

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief Aggregates information required for onboarding a device to its
 * customer AWS IoT account with the Onboarding service.
 */
typedef struct AwsIotOnboardingOnboardDeviceInfo
{
    const uint8_t * pDeviceCertificate; /**< @brief The certificate to onboard the device with. */
    size_t deviceCertificateLength;     /**< @brief The length of the certificate. */
    const char * ptemplateIdentifier;   /**< @brief The identifier of the template on the AWS IoT account used for
                                         * onboarding the device. */
    size_t templateIdentifierLength;    /**< @brief The length of the template identifier. */
    const void * pContextParameters;    /**< @brief The pre-encoded data to pass as device context to the server for
                                         * onboarding the device. */
    size_t contextParametersLength;     /**< @brief The length of the device context data. */
} AwsIotOnboardingOnboardDeviceInfo_t;


/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief Parameter to a Onboarding callback function.
 *
 * @paramfor Onboarding callback functions
 *
 * The Onboarding library passes this struct to a callback function whenever an
 * Onboarding operation completes successfully (i.e. a successful response is received from the server).
 *
 * The valid members of this struct are different based on
 * #AwsIotOnboardingCallbackParam_t.callbackType. If the callback type is
 * #AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_COMPLETE, then #AwsIotOnboardingCallbackParam_t.deviceCredentialsInfo
 * is valid. Otherwise, if the callback type is #AWS_IOT_ONBOARDING_ONBOARD_DEVICE_COMPLETE, then
 * #AwsIotOnboardingCallbackParam_t.onboardDeviceResponse is valid.
 *
 */
typedef struct AwsIotOnboardingCallbackParam
{
    AwsIotOnboardingCallbackType_t callbackType;

    union
    {
        /* Represents the new device credentials sent by the server. */
        struct
        {
            const char * pDeviceCertificate; /**< The new certificate for the device.*/
            size_t deviceCertificateLength;  /**< The size of the device certificate.*/
            const char * pCertificateId;     /**< The certificate ID associated with the new certificate,
                                              * @p pDeviceCertificate.*/
            size_t certificateIdLength;      /**< The length of the certificate ID.*/
            const uint8_t * pPrivateKey;     /**< The private key associated with the new certificate,
                                              * @p pDeviceCertificate.*/
            size_t privateKeyLength;         /**< The size of the private key.*/
        } deviceCredentialsInfo;

        /* Represents the server response to the request of onboarding device*/
        struct
        {
            const char * pClientId;     /**< The client ID received from the server. */
            size_t clientIdLength;      /**< The size of the client ID string. */
            const void * pDeviceConfig; /**< The device configuration data received from the server. NOTE: The encoded
                                         * device config information will be copied in the buffer. */
            size_t deviceConfigLength;  /**< The size of the encoded device configuration data. */
        } onboardDeviceResponse;
    } u;                                /**< @brief Valid member depends on callback type. */
} AwsIotOnboardingCallbackParam_t;

/**
 * @ingroup onboarding_datatypes_paramstructs
 * @brief User-specified parameter and callback function.
 *
 * @paramfor @ref onboarding_function_getdevicecredentials, @ref onboarding_function_onboarddevice
 *
 * Provides a function to be invoked on successful completion of an Onboarding operation.
 *
 * @initializer{AwsIotOnboardingCallbackInfo_t,AWS_IOT_ONBOARDING_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotOnboardingCallbackInfo
{
    void * userParam; /**< The user-provided parameter to be passed (as the first parameter) to the callback
                       * function(optional). */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotOnboardingCallbackInfo.userParam
     * @param[in] AwsIotOnboardingCallbackParam_t* Parsed server response of either device credentials
     * or onboarded device information.
     *
     * @see #AwsIotOnboardingCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         const AwsIotOnboardingCallbackParam_t * ); /*<** The user-provided callback to invoke with the
                                                                     #AwsIotOnboardingCallbackInfo.userParam data as the
                                                                     #first parameter. */
} AwsIotOnboardingCallbackInfo_t;


/*------------------------ Onboarding defined constants -------------------------*/

/* @[define_onboarding_initializers] */
#define AWS_IOT_ONBOARDING_CALLBACK_INFO_INITIALIZER          { 0 } /**< @brief Initializer for
                                                                     * #AwsIotOnboardingCallbackInfo_t. */
/** @brief Initializer for #AwsIotOnboardingOnboardDeviceInfo_t. */
#define AWS_IOT_ONBOARDING_ONBOARD_DEVICE_INFO_INITIALIZER    { 0 }
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
