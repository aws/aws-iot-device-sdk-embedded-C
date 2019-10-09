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
            #error "Asserts are enabled for MQTT, but IotMqtt_Assert is not defined"
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
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_TOPIC_FILTER \
    "certificates/create/"ONBOARDING_FORMAT

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
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC \
    "certificates/create/"ONBOARDING_FORMAT

/**
 * @brief The length of the MQTT request topic for the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC_LENGTH \
    ( ( uint16_t ) ( sizeof( ONBOARDING_GET_DEVICE_CREDENTIALS_REQUEST_TOPIC ) - 1 ) )

/**
 * @brief The key for the device certificate entry in the response payload of the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_PEM_STRING \
    "certificatePem"

/**
 * @brief The key for the certificate Id entry in the response payload of the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_CERTIFICATE_ID_STRING    "certificateId"

/**
 * @brief The key for the private key entry in the response payload of the GetDeviceCredentials service API.
 */
#define ONBOARDING_GET_DEVICE_CREDENTIALS_RESPONSE_PAYLOAD_PRIVATE_KEY_STRING       "privateKey"

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
 * @brief Functor for parsing response payload received from Onboarding service.
 * Parser that will de-serialize the server response and invoke the user callback passed to it.
 *
 * @param[in] responsePayload The response payload to parse.
 * @param[in] rsponsePayloadLength The length of the response payload.
 * @param[in] usercallback The user-provided callback to invoke on successful parsing of device credentials.
 */
typedef AwsIotOnboardingError_t ( * _onboardingServerResponseParser)( const void * responsePayload,
                                                                      size_t responsePayloadLength,
                                                                      const
                                                                      AwsIotOnboardingCallbackInfo_t
                                                                      * userCallback );

/**
 * @brief Internal structure representing the data of an Onboarding operation.
 */
typedef struct _onboardingOperationInfo
{
    AwsIotOnboardingError_t status;              /**< @brief Status of operation. */
    AwsIotOnboardingCallbackInfo_t userCallback; /**< @brief User-provided callback to be called on receiving a
                                                  * successful response from the server.*/
} _onboardingOperationInfo_t;

/**
 * @brief Internal structure representing a single Onboarding operation.
 */
typedef struct _onboardingOperation
{
    IotMutex_t lock;                    /**< @brief Must be acquired before modifying this operation object. */
    _onboardingOperationInfo_t info;    /**< @brief The Onboarding operation object that is protected by the above
                                         * mutex. */
    IotSemaphore_t responseReceivedSem; /**< @brief Semaphore to be used used by the synchronous API functions @ref
                                         * onboarding_function_getdevicecredentials and @ref
                                         * onboarding_function_onboarddevice. */
} _onboardingOperation_t;

extern uint32_t _AwsIotOnboardingMqttTimeoutMs;

#endif /* ifndef AWS_IOT_ONBOARDING_INTERNAL_H_ */
