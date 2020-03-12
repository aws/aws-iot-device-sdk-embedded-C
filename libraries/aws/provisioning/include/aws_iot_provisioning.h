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
 * @file aws_iot_provisioning.h
 * @brief User-facing functions of the Provisioning library.
 */

#ifndef AWS_IOT_PROVISIONING_H_
#define AWS_IOT_PROVISIONING_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Provisioning types include. */
#include "types/aws_iot_provisioning_types.h"

/* MQTT Types */
#include "types/iot_mqtt_types.h"

/*------------------------- AWS Provisioning library functions --------------------------*/

/**
 * @functionspage{provisioning,Provisioning library}
 * - @functionname{provisioning_function_init}
 * - @functionname{provisioning_function_createkeysandcertificate}
 * - @functionname{provisioning_function_createcertificatefromcsr}
 * - @functionname{provisioning_function_registerthing}
 * - @functionname{provisioning_function_cleanup}
 * - @functionname{provisioning_function_strerror}
 */

/**
 * @functionpage{AwsIotProvisioning_Init,provisioning,init}
 * @functionpage{AwsIotProvisioning_CreateKeysAndCertificate,provisioning,createkeysandcertificate}
 * @functionpage{AwsIotProvisioning_CreateCertificateFromCsr,provisioning,createcertificatefromcsr}
 * @functionpage{AwsIotProvisioning_RegisterThing,provisioning,registerthing}
 * @functionpage{AwsIotProvisioning_Cleanup,provisioning,cleanup}
 * @functionpage{AwsIotProvisioning_strerror,provisioning,strerror}
 */


/**
 * @brief One-time initialization function for the Provisioning library.
 *
 * This function performs internal setup of the Provisioning library. <b>It must be
 * called once (and only once) before calling any other Provisioning function.</b>
 * Calling this function more than once without first calling @ref
 * provisioning_function_cleanup may result in a crash.
 *
 * @param[in] mqttTimeout The amount of time (in milliseconds) that the Provisioning
 * library will wait for MQTT operations. Optional; set this to `0` to use
 * @ref AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS.
 *
 * @return One of the following:
 * - #AWS_IOT_PROVISIONING_SUCCESS
 * - #AWS_IOT_PROVISIONING_INIT_FAILED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref provisioning_function_cleanup
 */
/* @[declare_provisioning_init] */
AwsIotProvisioningError_t AwsIotProvisioning_Init( uint32_t mqttTimeout );
/* @[declare_provisioning_init] */

/**
 * @brief Requests a new public-private key pair and certificate for the device from the AWS IoT Core service and
 * invokes the passed user-callback with the credentials it receives from the server.
 *
 * @note The device should be connected to the user AWS IoT account over MQTT and the calling code should provide the
 * MQTT connection handle to the API for communicating with the server.
 *
 * @param[in] connection The MQTT connection handle to the user AWS IoT account, which will be used for
 * communicating with the server for creating new device credentials.
 * @param[in] flags The flags for configuring the behavior of the API. See the options available in the
 * aws_iot_provisioning_types.h file.
 * @param[in] timeoutMs The timeout (in milliseconds) for a response from the server. If there is a timeout, this
 * function returns #AWS_IOT_PROVISIONING_TIMEOUT.
 * @param[in] pResponseCallback The user-defined callback that will be invoked with the response from the server,
 * whether new credentials for the device in case of success, OR error response in case of server rejection of the
 * credentials generation request.
 * The callback should be defined appropriately for storing the credentials provided by the server on the device.
 * @warning Do not overwrite the existing Provisioning claim credentials with the new credentials provided by
 * the server. It is RECOMMENDED NOT to delete the certificate and private key used for the passed connection handle
 * until the device has been provisioned with a new certificate with the @ref provisioning_function_registerthing
 * function.
 * @return This function will return #AWS_IOT_PROVISIONING_SUCCESS upon success; otherwise,
 *   #AWS_IOT_PROVISIONING_NOT_INITIALIZED, if the API is called without initializing the Provisioning library (i.e.
 *   with a prior call to @ref AwsIotProvisioning_Init function.)
 *   #AWS_IOT_PROVISIONING_BAD_PARAMETER, if one or more input parameters are invalid.
 *   #AWS_IOT_PROVISIONING_NO_MEMORY, if there is insufficient memory for allocation in internal operations.
 *   #AWS_IOT_PROVISIONING_MQTT_ERROR, for errors from the MQTT stack.
 *   #AWS_IOT_PROVISIONING_TIMEOUT, if there is a timeout in waiting for the server response for the request to
 *   generate new credentials for the device.
 *   #AWS_IOT_PROVISIONING_SERVER_REFUSED, if the server rejects the request for generating device credentials.
 *   #AWS_IOT_PROVISIONING_BAD_RESPONSE, if the response from the server cannot be successfully parsed or comprehended.
 *   #AWS_IOT_PROVISIONING_INTERNAL_FAILURE, if any there are operation failures internal to the library.
 */
/* @[declare_provisioning_createkeysandcertificate] */
AwsIotProvisioningError_t AwsIotProvisioning_CreateKeysAndCertificate( IotMqttConnection_t connection,
                                                                       uint32_t flags,
                                                                       uint32_t timeoutMs,
                                                                       const AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t * pResponseCallback );
/* @[declare_provisioning_createkeysandcertificate] */

/**
 * @brief Requests the AWS IoT Core service for a certificate by sending a Certificate-Signing Request, and
 * invokes the provided user-defined response handler with the response it receives from the server.
 *
 * @note The device should be connected to the user AWS IoT account over MQTT and the calling code should provide the
 * MQTT connection handle to the API for communicating with the server.
 *
 * @param[in] connection The MQTT connection handle that will be used to communicate with AWS IoT Core for
 * the Certificate-Signing Request.
 * @param[in] operationQos The Quality of Service (QoS) level for the MQTT publish/subscribe communication with the server.
 * @param[in] pCertificateSigningRequest The PEM encoded string for the Certificate-Signing Request.
 * @param[in] csrLength The length of the Certificate-Signing Request string.
 * @param[in] timeoutMs The timeout (in milliseconds) for a response from the server. If there is a timeout, this
 * function returns #AWS_IOT_PROVISIONING_TIMEOUT.
 * @param[in] pResponseCallback The user-defined callback that will be invoked with the server's response to the CSR request.
 * The server can respond either with the new certificate information (in case of request acceptance) OR with error (in case of request
 * rejection).
 *
 * @note The callback is expected to store/retain the new certificate information from the server response, which will be required for
 * registering the device with @ref provisioning_function_registerthing function.
 *
 * @warning Do not overwrite the existing certificate (used for making the server connection) with the new certificate that is provided
 * by the server. It is RECOMMENDED to retain the Provisinoning claim credentials until the device has been provisioned with a new certificate
 * using the @ref provisioning_function_registerthing function.
 * @return This function will return #AWS_IOT_PROVISIONING_SUCCESS upon success; otherwise,
 *   #AWS_IOT_PROVISIONING_NOT_INITIALIZED, if the API is called without initializing the Provisioning library (i.e.
 *   with a prior call to @ref AwsIotProvisioning_Init function.)
 *   #AWS_IOT_PROVISIONING_BAD_PARAMETER, if one or more input parameters are invalid.
 *   #AWS_IOT_PROVISIONING_NO_MEMORY, if there is insufficient memory for allocation in internal operations.
 *   #AWS_IOT_PROVISIONING_MQTT_ERROR, for errors from the MQTT stack.
 *   #AWS_IOT_PROVISIONING_TIMEOUT, if there is a timeout in waiting for the server response for the request to
 *   generate new credentials for the device.
 *   #AWS_IOT_PROVISIONING_SERVER_REFUSED, if the server rejects the request for generating device credentials.
 *   #AWS_IOT_PROVISIONING_BAD_RESPONSE, if the response from the server cannot be successfully parsed or comprehended.
 *   #AWS_IOT_PROVISIONING_INTERNAL_FAILURE, if any there are operation failures internal to the library.
 */
/* @[declare_provisioning_createcertificatefromcsr] */
AwsIotProvisioningError_t AwsIotProvisioning_CreateCertificateFromCsr( IotMqttConnection_t connection,
                                                                       IotMqttQos_t operationQos,
                                                                       const char * pCertificateSigningRequest,
                                                                       size_t csrLength,
                                                                       uint32_t timeoutMs,
                                                                       const AwsIotProvisioningCreateCertificateFromCsrCallbackInfo_t * pResponseCallback );
/* @[declare_provisioning_createcertificatefromcsr] */

/**
 * @brief Requests the AWS IoT Core service to provision the device, and invokes the passed user-callback with the
 * response it receives from the service on provisioning the device.
 *
 * For provisioning the device, the service is expected to register the certificate, and optionally set up the Thing,
 * Attributes and other cloud settings based on the fleet provisioning template and device context information that are
 * passed to the API.
 *
 * @note The device should be connected to the user AWS IoT account over MQTT and the calling code should provide the
 * MQTT connection handle to the API for communicating with the server.
 *
 * Also, the AWS IoT account being connected to for provisioning the device SHOULD have a fleet provisioning template
 * created, whose template name should be passed to this API for requesting device provisioning.
 *
 * @param[in] connection The MQTT connection handle to the user AWS IoT account that will be used for
 * provisioning the device.
 * @param[in] pProvisioningDataInfo The data (including the certificate) that needs to be sent to the server for
 * provisioning the device.
 * @param[in] timeoutMs The timeout (in milliseconds) for a response from the server. If there is a timeout, this
 * function returns #AWS_IOT_PROVISIONING_TIMEOUT.
 * @param[in] pResponseCallback The user-defined functor that will be called with the response received from the server,
 * whether post-provisioning data in case of success OR error message in case of server rejection of provisioning
 * request.
 * @note In case of success response, the server may send device-specific configuration data, which will be provided as
 * a list of key-value pairs in the callback.
 * @return This function will return #AWS_IOT_PROVISIONING_SUCCESS upon success; otherwise,
 *   #AWS_IOT_PROVISIONING_NOT_INITIALIZED, if the API is called without initializing the Provisioning library (i.e.
 *   with a prior call to @ref AwsIotProvisioning_Init function.)
 *   #AWS_IOT_PROVISIONING_BAD_PARAMETER, if one or more input parameters are invalid.
 *   #AWS_IOT_PROVISIONING_NO_MEMORY, if there is insufficient memory for allocation in internal operations.
 *   #AWS_IOT_PROVISIONING_MQTT_ERROR, for errors from the MQTT stack.
 *   #AWS_IOT_PROVISIONING_TIMEOUT, if there is a timeout in waiting for the server response for the request to
 *   provision device.
 *   #AWS_IOT_PROVISIONING_SERVER_REFUSED, if the server rejects the request for provisioning the device.
 *   #AWS_IOT_PROVISIONING_BAD_RESPONSE, if the response from the server cannot be successfully parsed or comprehended.
 *   #AWS_IOT_PROVISIONING_INTERNAL_FAILURE, if any there are operation failures internal to the library.
 */
/* @[declare_provisioning_registerthing] */

AwsIotProvisioningError_t AwsIotProvisioning_RegisterThing( IotMqttConnection_t connection,
                                                            const AwsIotProvisioningRegisterThingRequestInfo_t * pProvisioningDataInfo,
                                                            uint32_t timeoutMs,
                                                            const AwsIotProvisioningRegisterThingCallbackInfo_t * pResponseCallback );
/* @[declare_provisioning_registerthing] */


/**
 * @brief One-time deinitialization function for the Provisioning library.
 *
 * This function frees resources taken in @ref provisioning_function_init.
 * It should be called to clean up the Provisioning library. After this function returns,
 * @ref provisioning_function_init must be called again before calling any other Provisioning
 * function.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref provisioning_function_init
 */
/* @[declare_provisioning_cleanup] */
void AwsIotProvisioning_Cleanup( void );
/* @[declare_provisioning_cleanup] */

/*------------------------- Provisioning helper functions -------------------------*/

/**
 * @brief Returns a string that describes an #AwsIotProvisioningError_t.
 *
 * Like POSIX's `strerror`, this function returns a string describing a return
 * code. In this case, the return code is a Provisioning library error code, `status`.
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
/* @[declare_provisioning_strerror] */
const char * AwsIotProvisioning_strerror( AwsIotProvisioningError_t status );
/* @[declare_provisioning_strerror] */

#endif /* ifndef AWS_IOT_PROVISIONING_H_ */
