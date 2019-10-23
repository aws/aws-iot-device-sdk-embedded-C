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
 * @file aws_iot_onboarding.h
 * @brief User-facing functions of the Onboarding library.
 */

#ifndef AWS_IOT_ONBOARDING_H_
#define AWS_IOT_ONBOARDING_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Onboarding types include. */
#include "types/aws_iot_onboarding_types.h"

/* MQTT Types */
#include "types/iot_mqtt_types.h"

/*------------------------- AWS Onboarding library functions --------------------------*/

/**
 * @functionspage{onboarding,Onboarding library}
 * - @functionname{onboard_function_init}
 * - @functionname{onboard_function_getdevicecredentials}
 * - @functionname{onboard_function_onboarddevice}
 * - @functionname{onboard_function_cleanup}
 * - @functionname{onboard_function_strerror}
 */

/**
 * @functionpage{AwsIotOnboard_Init,onboard,init}
 * @functionpage{AwsIotOnboard_GetDeviceCredentials,onboard,getdevicecredentials}
 * @functionpage{AwsIotOnboard_OnboardDevice,onboard,onboarddevice}
 * @functionpage{AwsIotOnboard_Cleanup,onboard,cleanup}
 * @functionpage{AwsIotOnboard_strerror,onboard,strerror}
 */

/* @[declare_onboarding_init] */

/**
 * @brief One-time initialization function for the Onboarding library.
 *
 * This function performs internal setup of the Onboarding library. <b>It must be
 * called once (and only once) before calling any other Onboarding function.</b>
 * Calling this function more than once without first calling @ref
 * onboarding_function_cleanup may result in a crash.
 *
 * @param[in] mqttTimeout The amount of time (in milliseconds) that the Onboarding
 * library will wait for MQTT operations. Optional; set this to `0` to use
 * @ref AWS_IOT_ONBOARDING_DEFAULT_MQTT_TIMEOUT_MS.
 *
 * @return One of the following:
 * - #AWS_IOT_ONBOARDING_SUCCESS
 * - #AWS_IOT_ONBOARDING_INIT_FAILED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref onboarding_function_cleanup
 */
/* @[declare_onboarding_init] */
AwsIotOnboardingError_t AwsIotOnboarding_Init( uint32_t mqttTimeout );
/* @[declare_onboarding_init] */


/**
 * @brief Requests new device credentials from the Onboarding service and invokes the user provided callback, that is
 * passed to the API, with the credentials it receives from the server.
 *
 * The device should be connected to the user AWS IoT account and provide the MQTT connection handle for fulfilling this
 * credential generation operation.
 *
 * @param[in] onboardingConnection The MQTT connection handle to the user AWS IoT account, which will be used for
 * onboarding.
 * @param[in] flags The flags for configuring the behavior of the API. See the options available in the
 * aws_iot_onboarding_types.h file.
 * @param[in] timeoutMs The timeout for a response from the server. If there is a timeout, this function returns
 * #AWS_IOT_ONBOARDING_TIMEOUT.
 * @param[in] deviceCredentialsResponseCallback The user-defined functor that will be called on receiving the
 * credentials from the server.
 * The callback should be defined appropriately for storing the credentials provided by the server on the device.
 * @warning Do not overwrite the Onboarding claim credentials with the new credentials provided by the server. It is
 * RECOMMENDED NOT to overwrite the certificate used for the passed connection handle until the device has been
 * onboarded
 * with a new onboarding certificate.
 * @return This function will return #AWS_IOT_ONBOARDING_SUCCESS upon success; otherwise,
 *   #AWS_IOT_ONBOARDING_BAD_PARAMETER, if one or more input parameters are invalid.
 *   #AWS_IOT_ONBOARDING_NO_MEMORY, if there are memory allocation errors.
 *   #AWS_IOT_ONBOARDING_MQTT_ERROR, for errors from the MQTT stack.
 *   #AWS_IOT_ONBOARDING_TIMEOUT, if there is a timeout in any of the internal operations with the server.
 *   #AWS_IOT_ONBOARDING_SERVER_REFUSED, if the server rejects the request for sending device credentials.
 *   #AWS_IOT_ONBOARDING_BAD_RESPONSE, if the response from the server cannot be successfully parsed or comprehended.
 *   #AWS_IOT_ONBOARDING_INTERNAL_FAILURE, if any there are operation errors internal to the library.
 * @see @ref onboard_function_getdevicecredentials
 */
AwsIotOnboardingError_t AwsIotOnboarding_GetDeviceCredentials( IotMqttConnection_t
                                                               onboardingConnection,
                                                               uint32_t flags,
                                                               uint32_t timeoutMs,
                                                               const AwsIotOnboardingCallbackInfo_t * deviceCredentialsResponseCallback );
/* @[declare_onboarding_getdevicecredentials] */

/**
 * @brief Requests the Onboarding service to onboard the device with the certificate and extra information that is
 * passed to the API, and returns the information received from the service on onboarding the device.
 *
 * The device should use this API to register its credentials for onboarding itself.
 *
 * @param[in] onboardingConnection The MQTT connection handle to the user AWS IoT account that will be used for
 * onboarding the device.
 * @param[in] pOnboardingDataInfo The configuration parameters that the device needs to be onboarded with.
 * @param[in] timeoutMs The timeout for a response from the server. If there is a timeout, this function returns
 * #AWS_IOT_ONBOARDING_TIMEOUT.
 * @param[in] responseCallback The user-defined functor that will be called with the data (that includes the device
 * configuration) received from the server, if the device is successfully onboarded.
 * @note The device configuration data, that is obtained from the server, will be passes in the serialized format to the
 * callback.
 * @return This function will return #AWS_IOT_ONBOARDING_SUCCESS upon success; otherwise,
 *   #AWS_IOT_ONBOARDING_BAD_PARAMETER, if one or more input OR output parameters are invalid.
 *   #AWS_IOT_ONBOARDING_NO_MEMORY, if there is insufficient memory size for copying the config data.
 *   #AWS_IOT_ONBOARDING_MQTT_ERROR, for errors from the MQTT stack.
 *   #AWS_IOT_ONBOARDING_TIMEOUT, if there is a timeout in any of the internal operations with the server.
 *   #AWS_IOT_ONBOARDING_SERVER_REFUSED, if the server rejects the request for onboarding the device.
 *   #AWS_IOT_ONBOARDING_BAD_RESPONSE, if the response from the server cannot be successfully parsed or comprehended.
 *   #AWS_IOT_ONBOARDING_INTERNAL_FAILURE, if any there are operation errors internal to the library.
 */
/* @[declare_onboarding_onboarddevice] */

AwsIotOnboardingError_t AwsIotOnboarding_OnboardDevice( IotMqttConnection_t onboardingConnection,
                                                        const AwsIotOnboardingOnboardDeviceRequestInfo_t *
                                                        pOnboardingDataInfo,
                                                        uint32_t timeoutMs,
                                                        const AwsIotOnboardingCallbackInfo_t * responseCallback );
/* @[declare_onboarding_onboarddevice] */


/**
 * @brief One-time deinitialization function for the Onboarding library.
 *
 * This function frees resources taken in @ref onboarding_function_init.
 * It should be called to clean up the Onboarding library. After this function returns,
 * @ref onboarding_function_init must be called again before calling any other Onboarding
 * function.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref onboarding_function_init
 */
/* @[declare_onboarding_cleanup] */
void AwsIotOnboarding_Cleanup( void );
/* @[declare_onboarding_cleanup] */

/*------------------------- Onboarding helper functions -------------------------*/

/**
 * @brief Returns a string that describes an #AwsIotOnboardingError_t.
 *
 * Like POSIX's `strerror`, this function returns a string describing a return
 * code. In this case, the return code is a Onboarding library error code, `status`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] status The status to describe.
 *
 * @return A read-only string that describes `status`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_onboarding_strerror] */
const char * AwsIotOnboarding_strerror( AwsIotOnboardingError_t status );
/* @[declare_onboarding_strerror] */

#endif /* ifndef AWS_IOT_ONBOARDING_H_ */
