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
 * @file aws_iot_tests_provisioning_api.c
 * @brief Tests for the user-facing API functions (declared in aws_iot_provisioning.h).
 */

/* The config header is always included first. */
#include "iot_config.h"

/* SDK initialization include. */
#include "iot_init.h"

/* MQTT include. */
#include "iot_mqtt.h"
#include "iot_mqtt_serialize.h"

/* Provisioning internal include. */
#include "private/aws_iot_provisioning_internal.h"

/* MQTT mock include. */
#include "iot_tests_mqtt_mock.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/**
 * @brief Context for calls to the network receive function.
 */
typedef struct _receiveContext
{
    const uint8_t * pData; /**< @brief The data to receive. */
    size_t dataLength;     /**< @brief Length of data. */
    size_t dataIndex;      /**< @brief Next byte of data to read. */
} _receiveContext_t;

/**
 * @brief Context for calls to the server response simulating thread, #_simulateServerResponse .
 */
typedef struct _serverResponseThreadContext
{
    const char * pPublishTopic;   /**< @brief The topic to simulate server PUBLISH on. */
    size_t publishTopicLength;    /**< @brief The length of the server's PUBLISH topic. */
    const uint8_t * pPublishData; /**< @brief The data to send as PUBLISH payload on the topic. */
    size_t publishDataLength;     /**< @brief The length of the PUBLISh payload. */
} _serverResponseThreadContext_t;

/**
 * @brief Test user-callback that validates the credentials parsed and provided by the
 * @provisioning_function_registerthing API.
 * This is passed as a member of #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t type.
 */
static void _testCreateKeysAndCertificateCallback( void * contextParam,
                                                   const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo );

/**
 * @brief Test user-callback that validates the provision device response parsed and provided by the
 * @provisioning_function_registerthing API.
 * This is passed as a member of #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t type.
 */
static void _testRegisterThingCallback( void * contextParam,
                                        const AwsIotProvisioningRegisterThingResponse_t * pResponseInfo );

/**
 * @brief Invokes the MQTT receive callback to simulate a response received from
 * the network.
 */
static void _simulateServerResponse( void * pArgument );

/**
 * @brief Dummy user-callback to pass in #AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t.
 */
static void _dummyKeysAndCertificateCallback( void * contextParam,
                                              const AwsIotProvisioningCreateKeysAndCertificateResponse_t * responseInfo );

/**
 * @brief Dummy user-callback to pass in #AwsIotProvisioningRegisterThingCallbackInfo_t.
 */
static void _dummyRegisterThingCallback( void * contextParam,
                                         const AwsIotProvisioningRegisterThingResponse_t * responseInfo );

/**
 * @brief Common test logic that simulates server response and calls the #AwsIotProvisioning_CreateKeysAndCertificate
 * API to
 * test.
 *
 * @param[in] pServerResponseInfo The server response to inject into the MQTT stack for the test case.
 * @param[in] serverResponseTimerPeriodMs The server response delay (in milliseconds) to simulate.
 * @param[in] pTestCallback The callback object to pass to the API under test.
 * @param[in] expectedStatus This will be compared against the returned status from the API call.
 */
static void _testCreateKeysAndCertificateAPIWithServerResponse( _serverResponseThreadContext_t * pServerResponseInfo,
                                                                uint32_t serverResponseTimerPeriodMs,
                                                                const AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t * pTestCallback,
                                                                AwsIotProvisioningError_t expectedStatus );

/**
 * @brief Common test logic that simulates server response and calls the #AwsIotProvisioning_RegisterThing API to test.
 *
 * @param[in] pServerResponseInfo The server response to inject into the MQTT stack for the test case.
 * @param[in] serverResponseTimerPeriodMs The server response delay (in milliseconds) to simulate.
 * @param[in] pTestCallback The callback object to pass to the API under test.
 * @param[in] expectedStatus This will be compared against the returned status from the API call.
 */
static void _testRegisterThingAPIWithServerResponse( _serverResponseThreadContext_t * pServerResponseInfo,
                                                     uint32_t serverResponseTimerPeriodMs,
                                                     const AwsIotProvisioningRegisterThingCallbackInfo_t * pTestCallback,
                                                     AwsIotProvisioningError_t expectedStatus );

/*-----------------------------------------------------------*/

/**
 * @brief The MQTT connection shared among the tests.
 */
static IotMqttConnection_t _pMqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/**
 * @brief Timer used to simulate a PUBLISH response from the Provisioning server.
 */
static IotTimer_t _serverResponseTimer;

/**
 * @brief The server response timeout value for operation APIs of the Provisioning library.
 */
static const uint32_t _testProvisioningApiTimeoutMs = 100;

/**
 * @brief The timer period after which the "server response simulating" thread should be run.
 */
static const uint32_t _testProvisioningServerResponseThreadTimeoutMs = 90;

/**
 * @brief The accepted response topic for the Provisioning CreateKeysAndCertificate service API.
 */
static const char * _createKeysAndCertificateRejectedResponseTopic =
    PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER "/rejected";

/**
 * @brief The rejected response topic for the ProvisioningDevice service API.
 */
static const char * _createKeysAndCertificateAcceptedResponseTopic =
    PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_RESPONSE_TOPIC_FILTER "/accepted";

/**
 * @brief Sample CBOR encoded response of Provisioning CreateKeysAndCertificate service API containing mock certificate
 * and private key data.
 */
static const uint8_t _sampleCreateKeysAndCertificateServerResponsePayload[] =
{
    0xA4,                                                                               /* # map( 4 ) */
    0x6E,                                                                               /* # text( 14 ) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x50, 0x65, 0x6D, /* # "certificatePem" */
    0x67,                                                                               /* # text(7) */
    0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,                                           /* # "abcdefg" */
    0x6D,                                                                               /* # text(13) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x49, 0x64,       /* # "certificateId" */
    0x66,                                                                               /* # text(6) */
    0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D,                                                 /* # "hijklm" */
    0x6A,                                                                               /* # text( 10 ) */
    0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65, 0x4B, 0x65, 0x79,                         /* # "privateKey" */
    0x67,                                                                               /* # text(7) */
    0x53, 0x65, 0x63, 0x72, 0x65, 0x74, 0x21,                                           /*# "Secret!" */
    0x78, 0x19,                                                                         /*# text(25) */
    0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x4F, 0x77, 0x6E,
    0x65, 0x72, 0x73, 0x68, 0x69, 0x70, 0x54, 0x6F, 0x6B, 0x65, 0x6E,                   /*# "certificateOwnershipToken"
                                                                                         * */
    0x66,                                                                               /*# text(6) */
    0x54, 0x6F, 0x6B, 0x65, 0x6E, 0x21                                                  /*# "Token!" */
};

/**
 * @brief Expected parameters to the user-callback by the Provisioning library APIs.
 */
static AwsIotProvisioningCreateKeysAndCertificateResponse_t _expectedCreateKeysAndCertificateCallbackParams =
{
    .statusCode                                    = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED,
    .u.acceptedResponse.pDeviceCertificate         = ( const char * )
                                                     &_sampleCreateKeysAndCertificateServerResponsePayload[ 17 ],
    .u.acceptedResponse.deviceCertificateLength    = 7,
    .u.acceptedResponse.pCertificateId             = ( const char * )
                                                     &_sampleCreateKeysAndCertificateServerResponsePayload[ 39 ],
    .u.acceptedResponse.certificateIdLength        = 6,
    .u.acceptedResponse.pPrivateKey                = ( const char * )
                                                     &_sampleCreateKeysAndCertificateServerResponsePayload[ 57 ],
    .u.acceptedResponse.privateKeyLength           = 7,
    .u.acceptedResponse.pCertificateOwnershipToken = ( const char * )
                                                     &_sampleCreateKeysAndCertificateServerResponsePayload[ 92 ],
    .u.acceptedResponse.ownershipTokenLength       = 6,
};

/**
 * @brief Callback object with #_expectedCreateKeysAndCertificateCallbackParams as context parameter to test
 * #AwsIotProvisioning_CreateKeysAndCertificate API.
 */
static const AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t _acceptedResponseCallbackForCreateKeysAndCertificateAPI =
{
    .userParam = &_expectedCreateKeysAndCertificateCallbackParams,
    .function  = _testCreateKeysAndCertificateCallback
};

/**
 * @brief Certificate ID for Provisioning's RegisterThing API tests.
 */
static const char _testCertificateId[] = "TestCertificateID";

/**
 * @brief Token string for Provisioning's RegisterThing API tests.
 */
static const char _testCertificateToken[] = "TestToken";

/**
 * @brief Template ID for Provisioning's RegisterThing API tests.
 */
#define _testTemplateName    "TEST_TEMPLATE"

/**
 * @brief The rejected response topic for the Provisioning RegisterThing service API.
 */
static const char * _registerThingAcceptedResponseTopic = "$aws/provisioning-templates/"_testTemplateName
                                                          "/provision/cbor/accepted";

/**
 * @brief The accepted response topic for the Provisioning RegisterThing service API.
 */
static const char * _registerThingRejectedResponseTopic = "$aws/provisioning-templates/"_testTemplateName
                                                          "/provision/cbor/rejected";

/**
 * @brief Sample CBOR encoded response of Provisioning's RegisterThing service API containing device configuration and
 * Iot Thing name
 * data.
 */
static const uint8_t _sampleRegisterThingResponsePayload[] =
{
    0xA2,                                                             /* # map(2) */
    0x73,                                                             /* # text(19) */
    0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61, 0x74,
    0x69, 0x6F, 0x6E,                                                 /* # "deviceConfiguration" */
    0xBF,                                                             /* # map(2) */
    0x6B,                                                             /* # text(11) */
    0x46, 0x61, 0x6C, 0x6C, 0x62, 0x61, 0x63, 0x6B, 0x55, 0x72, 0x6C, /* # "FallbackUrl" */
    0x78, 0x21,                                                       /* # text(33) */
    0x68, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x77, 0x77, 0x77,
    0x2E, 0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x63, 0x6F,
    0x6D, 0x2F, 0x74, 0x65, 0x73, 0x74, 0x2D, 0x73, 0x69, 0x74, 0x65, /* # "https://www.example.com/test-site" */
    0x6B,                                                             /* # text(11) */
    0x4C, 0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x55, 0x72, 0x6C, /* # "LocationUrl" */
    0x73,                                                             /* # text(19) */
    0x68, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x65, 0x78, 0x61,
    0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x61, 0x77, 0x73,                   /* # "https://example.aws" */
    0xFF,
    0x69,                                                             /* # text(9) */
    0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65,             /* # "thingName" */
    0x69,                                                             /* # text(9) */
    0x54, 0x65, 0x73, 0x74, 0x54, 0x68, 0x69, 0x6E, 0x67,             /* # "TestThing" */
    0x68                                                              /* # text(8) */
};

static const AwsIotProvisioningResponseDeviceConfigurationEntry_t _expectedDeviceConfigList[] =
{
    {
        ( const char * ) &_sampleRegisterThingResponsePayload[ 23 ],
        11,
        ( const char * ) &_sampleRegisterThingResponsePayload[ 36 ],
        33
    },
    {
        ( const char * ) &_sampleRegisterThingResponsePayload[ 70 ],
        11,
        ( const char * ) &_sampleRegisterThingResponsePayload[ 82 ],
        19
    }
};

/**
 * @brief Expected parameters that should be passed to the user-callback provided to the
 *#AwsIotProvisioning_RegisterThing
 * API.
 */
static AwsIotProvisioningRegisterThingResponse_t _expectedRegisterThingCallbackParams =
{
    .statusCode                                   = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED,
    .u.acceptedResponse.pThingName                = ( const char * ) &_sampleRegisterThingResponsePayload[ 113 ],
    .u.acceptedResponse.thingNameLength           = 9,
    .u.acceptedResponse.pDeviceConfigList         = _expectedDeviceConfigList,
    .u.acceptedResponse.numOfConfigurationEntries = sizeof( _expectedDeviceConfigList ) /
                                                    sizeof( AwsIotProvisioningResponseDeviceConfigurationEntry_t )
};

/**
 * @brief Callback object with #_expectedRegisterThingCallbackParams as context parameter to test
 * #AwsIotProvisioning_RegisterThing API.
 */
static const AwsIotProvisioningRegisterThingCallbackInfo_t _acceptedResponseCallbackForRegisterThingAPI =
{
    .userParam = &_expectedRegisterThingCallbackParams,
    .function  = _testRegisterThingCallback
};

/**
 * @brief Sample CBOR encoded payload for "rejected" response from server.
 */
static const uint8_t _sampleRejectedServerResponsePayload[] =
{
    0xA3,                                                                               /*# map(3) */
    0x6A,                                                                               /*# text(10) */
    0x73, 0x74, 0x61, 0x74, 0x75, 0x73, 0x43, 0x6F, 0x64, 0x65,                         /*# "statusCode" */
    0x19, 0x01, 0xF4,                                                                   /*# unsigned(500) */
    0x69,                                                                               /*# text(9) */
    0x65, 0x72, 0x72, 0x6F, 0x72, 0x43, 0x6F, 0x64, 0x65,                               /*# "errorCode" */
    0x6E,                                                                               /*# text(14) */
    0x49, 0x6E, 0x76, 0x61, 0x6C, 0x69, 0x64, 0x50, 0x61, 0x79, 0x6C, 0x6F, 0x61, 0x64, /*# "InvalidPayload" */
    0x6C,                                                                               /*# text(12) */
    0x65, 0x72, 0x72, 0x6F, 0x72, 0x4D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65,             /*# "errorMessage" */
    0x65,                                                                               /*# text(5) */
    0x4F, 0x6F, 0x70, 0x73, 0x21,                                                       /*# "Oops!" */
};

/*-----------------------------------------------------------*/

static void _dummyKeysAndCertificateCallback( void * contextParam,
                                              const AwsIotProvisioningCreateKeysAndCertificateResponse_t * responseInfo )
{
    ( void ) contextParam;
    ( void ) responseInfo;
}

/*-----------------------------------------------------------*/

static void _dummyRegisterThingCallback( void * contextParam,
                                         const AwsIotProvisioningRegisterThingResponse_t * responseInfo )
{
    ( void ) contextParam;
    ( void ) responseInfo;
}

/*-----------------------------------------------------------*/

static void _testCreateKeysAndCertificateCallback( void * contextParam,
                                                   const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    AwsIotProvisioningCreateKeysAndCertificateResponse_t * pExpectedParams =
        ( AwsIotProvisioningCreateKeysAndCertificateResponse_t * ) contextParam;

    AwsIotProvisioning_Assert( pExpectedParams->statusCode == pResponseInfo->statusCode );

    switch( pResponseInfo->statusCode )
    {
        case AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED:
            AwsIotProvisioning_Assert(
                pExpectedParams->u.acceptedResponse.deviceCertificateLength ==
                pResponseInfo->u.acceptedResponse.deviceCertificateLength );
            AwsIotProvisioning_Assert( 0 == memcmp(
                                           pExpectedParams->u.acceptedResponse.pDeviceCertificate,
                                           pResponseInfo->u.acceptedResponse.pDeviceCertificate,
                                           pExpectedParams->u.acceptedResponse.deviceCertificateLength ) );
            AwsIotProvisioning_Assert(
                pExpectedParams->u.acceptedResponse.certificateIdLength ==
                pResponseInfo->u.acceptedResponse.certificateIdLength );
            AwsIotProvisioning_Assert( 0 == memcmp(
                                           pExpectedParams->u.acceptedResponse.pCertificateId,
                                           pResponseInfo->u.acceptedResponse.pCertificateId,
                                           pExpectedParams->u.acceptedResponse.certificateIdLength ) );
            AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.privateKeyLength ==
                                       pResponseInfo->u.acceptedResponse.privateKeyLength );
            AwsIotProvisioning_Assert( 0 == memcmp(
                                           pExpectedParams->u.acceptedResponse.pPrivateKey,
                                           pResponseInfo->u.acceptedResponse.pPrivateKey,
                                           pExpectedParams->u.acceptedResponse.privateKeyLength ) );
            AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.ownershipTokenLength ==
                                       pResponseInfo->u.acceptedResponse.ownershipTokenLength );
            AwsIotProvisioning_Assert( 0 == memcmp(
                                           pExpectedParams->u.acceptedResponse.pCertificateOwnershipToken,
                                           pResponseInfo->u.acceptedResponse.pCertificateOwnershipToken,
                                           pExpectedParams->u.acceptedResponse.ownershipTokenLength ) );
            break;

        default:
            AwsIotProvisioning_Assert( false );
    }
}

static void _testRegisterThingCallback( void * contextParam,
                                        const AwsIotProvisioningRegisterThingResponse_t * pResponseInfo )
{
    AwsIotProvisioningRegisterThingResponse_t * pExpectedParams =
        ( AwsIotProvisioningRegisterThingResponse_t * ) contextParam;

    AwsIotProvisioning_Assert( pExpectedParams->statusCode == pResponseInfo->statusCode );

    switch( pResponseInfo->statusCode )
    {
        case AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED:

            AwsIotProvisioning_Assert(
                pExpectedParams->u.acceptedResponse.thingNameLength ==
                pResponseInfo->u.acceptedResponse.thingNameLength );

            if( pExpectedParams->u.acceptedResponse.thingNameLength > 0 )
            {
                AwsIotProvisioning_Assert( 0 == memcmp(
                                               pExpectedParams->u.acceptedResponse.pThingName,
                                               pResponseInfo->u.acceptedResponse.pThingName,
                                               pExpectedParams->u.acceptedResponse.thingNameLength ) );
            }

            AwsIotProvisioning_Assert(
                pExpectedParams->u.acceptedResponse.numOfConfigurationEntries ==
                pResponseInfo->u.acceptedResponse.numOfConfigurationEntries );

            for( size_t index = 0; index < pExpectedParams->u.acceptedResponse.numOfConfigurationEntries;
                 index++ )
            {
                AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.pDeviceConfigList[ index ].keyLength ==
                                           pResponseInfo->u.acceptedResponse.pDeviceConfigList[ index ].keyLength );
                AwsIotProvisioning_Assert( 0 == memcmp(
                                               pExpectedParams->u.acceptedResponse.pDeviceConfigList[ index ].pKey,
                                               pResponseInfo->u.acceptedResponse.pDeviceConfigList[ index ].pKey,
                                               pExpectedParams->u.acceptedResponse.pDeviceConfigList[ index ].keyLength ) );
                AwsIotProvisioning_Assert( pExpectedParams->u.acceptedResponse.pDeviceConfigList[ index ].valueLength ==
                                           pResponseInfo->u.acceptedResponse.pDeviceConfigList[ index ].valueLength );
                AwsIotProvisioning_Assert( 0 == memcmp(
                                               pExpectedParams->u.acceptedResponse.pDeviceConfigList[ index ].pValue,
                                               pResponseInfo->u.acceptedResponse.pDeviceConfigList[ index ].pValue,
                                               pExpectedParams->u.acceptedResponse.pDeviceConfigList[ index ].valueLength ) );
            }

            break;

        default:
            AwsIotProvisioning_Assert( false );
    }
}

/*-----------------------------------------------------------*/

static void _simulateServerResponse( void * pArgument )
{
    _serverResponseThreadContext_t * context = pArgument;
    _receiveContext_t receiveContext = { 0 };
    uint8_t * pPublishDataBuffer = NULL;
    size_t publishPacketSize = 0;
    size_t publishRemainingLength = 0;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    uint16_t publishPacketIdentifier;

    publishInfo.qos = IOT_MQTT_QOS_0;
    /* Set the server response.*/
    publishInfo.pPayload = context->pPublishData;
    publishInfo.payloadLength = context->publishDataLength;
    /* Set the operation topic name. */
    publishInfo.pTopicName = context->pPublishTopic;
    publishInfo.topicNameLength = context->publishTopicLength;

    /* Get the size of buffer needed to store the serialized MQTT packet (that will simulate server response). */
    TEST_ASSERT_EQUAL_MESSAGE( IOT_MQTT_SUCCESS, IotMqtt_GetPublishPacketSize( &publishInfo,
                                                                               &publishRemainingLength,
                                                                               &publishPacketSize ),
                               "Could not obtain buffer size required for storing PUBLISH packet "
                               "(that would be used for injecting Provisioning service response" );

    /* Allocate the buffer for serializing PUBLISH data. */
    pPublishDataBuffer = IotTest_Malloc( publishPacketSize );
    TEST_ASSERT_MESSAGE( pPublishDataBuffer != NULL, "Memory allocation for PUBLISH packet buffer failed. "
                                                     "Buffer would be used for injecting Provisioning server response" );

    TEST_ASSERT_EQUAL_MESSAGE( IOT_MQTT_SUCCESS, IotMqtt_SerializePublish( &publishInfo,
                                                                           publishRemainingLength,
                                                                           &publishPacketIdentifier,
                                                                           NULL,
                                                                           pPublishDataBuffer,
                                                                           publishPacketSize ),
                               "Could not generate serialized publish data for injecting Provisioning server response" );

    receiveContext.pData = pPublishDataBuffer;
    receiveContext.dataLength = publishPacketSize;

    /* Call the MQTT receive callback to process the ACK packet. */
    IotMqtt_ReceiveCallback( ( IotNetworkConnection_t ) &receiveContext, _pMqttConnection );

    /* Release the PUBLISH packet buffer. */
    IotTest_Free( pPublishDataBuffer );
}

/*-----------------------------------------------------------*/

static void _testCreateKeysAndCertificateAPIWithServerResponse( _serverResponseThreadContext_t * pServerResponseInfo,
                                                                uint32_t serverResponseTimerPeriodMs,
                                                                const AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t * pTestCallback,
                                                                AwsIotProvisioningError_t expectedStatus )
{
    TEST_ASSERT_EQUAL_INT( true, IotClock_TimerCreate( &_serverResponseTimer,
                                                       _simulateServerResponse,
                                                       pServerResponseInfo ) );
    ( void ) IotClock_TimerArm( &_serverResponseTimer,
                                serverResponseTimerPeriodMs,
                                0 );

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( expectedStatus, AwsIotProvisioning_CreateKeysAndCertificate( _pMqttConnection,
                                                                                    0,
                                                                                    _testProvisioningApiTimeoutMs,
                                                                                    pTestCallback ) );
    IotClock_TimerDestroy( &_serverResponseTimer );
}

static void _testRegisterThingAPIWithServerResponse( _serverResponseThreadContext_t * pServerResponseInfo,
                                                     uint32_t serverResponseTimerPeriodMs,
                                                     const AwsIotProvisioningRegisterThingCallbackInfo_t * pTestCallback,
                                                     AwsIotProvisioningError_t expectedStatus )
{
    AwsIotProvisioningRegisterThingRequestInfo_t requestInfo;

    TEST_ASSERT_EQUAL_INT( true, IotClock_TimerCreate( &_serverResponseTimer,
                                                       _simulateServerResponse,
                                                       pServerResponseInfo ) );
    ( void ) IotClock_TimerArm( &_serverResponseTimer,
                                serverResponseTimerPeriodMs,
                                0 );

    requestInfo.pDeviceCertificateId = _testCertificateId;
    requestInfo.deviceCertificateIdLength = strlen( _testCertificateId );
    requestInfo.pCertificateOwnershipToken = _testCertificateToken;
    requestInfo.ownershipTokenLength = strlen( _testCertificateToken );
    requestInfo.pTemplateName = _testTemplateName;
    requestInfo.templateNameLength = strlen( _testTemplateName );
    requestInfo.pParametersStart = NULL;
    requestInfo.numOfParameters = 0;

    /* Call the API under test. */
    TEST_ASSERT_EQUAL( expectedStatus, AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                                                         &requestInfo,
                                                                         _testProvisioningApiTimeoutMs,
                                                                         pTestCallback ) );


    IotClock_TimerDestroy( &_serverResponseTimer );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Provisioning API tests.
 */
TEST_GROUP( Provisioning_Unit_API );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Provisioning API tests.
 */
TEST_SETUP( Provisioning_Unit_API )
{
    /* Initialize SDK. */
    TEST_ASSERT_EQUAL_INT( true, IotSdk_Init() );

    /* Initialize the MQTT library. */
    TEST_ASSERT_EQUAL( IOT_MQTT_SUCCESS, IotMqtt_Init() );

    /* Initialize the Provisioning library. */
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, AwsIotProvisioning_Init( 0 ) );

    /* Initialize MQTT mock. */
    TEST_ASSERT_EQUAL_INT( true, IotTest_MqttMockInit( &_pMqttConnection ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Provisioning API tests.
 */
TEST_TEAR_DOWN( Provisioning_Unit_API )
{
    /* Clean up MQTT mock. */
    IotTest_MqttMockCleanup();

    /* Clean up libraries. */
    AwsIotProvisioning_Cleanup();
    IotMqtt_Cleanup();
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Provisioning API tests.
 */
TEST_GROUP_RUNNER( Provisioning_Unit_API )
{
    RUN_TEST_CASE( Provisioning_Unit_API, Init );
    RUN_TEST_CASE( Provisioning_Unit_API, StringCoverage );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPIInvalidParameters );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPICalledWithoutInit );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPINoServerResponse );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPIRejectedResponse );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPICorruptDataInResponse );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPINominalSuccess );
    RUN_TEST_CASE( Provisioning_Unit_API, CreateKeysAndCertificateAPIServerResponseAfterTimeout )
    RUN_TEST_CASE( Provisioning_Unit_API,
                   CreateKeysAndCertificateAPIServerResponseAndTimeoutRaceCondition );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPIInvalidParameters );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPICalledWithoutInit );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPINoServerResponse );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPIRejectedResponse );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPICorruptDataInResponse );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPINominalSuccess );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPIServerResponseWithoutDeviceConfiguration );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPIServerResponseWithoutThingName );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPIServerResponseAfterTimeout );
    RUN_TEST_CASE( Provisioning_Unit_API, RegisterThingAPIServerResponseAndTimeoutRaceCondition );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the function @ref provisioning_function_init.
 */
TEST( Provisioning_Unit_API, Init )
{
    int32_t i = 0;
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    /* Check that test set up set the default value. */
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotProvisioningMqttTimeoutMs );

    /* The Provisioning library was already initialized by test set up. Clean it up
     * before running this test. */
    AwsIotProvisioning_Cleanup();

    /* Set a MQTT timeout. */
    AwsIotProvisioning_Init( AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS + 1 );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS + 1,
                       _AwsIotProvisioningMqttTimeoutMs );

    /* Cleanup should restore the default MQTT timeout. */
    AwsIotProvisioning_Cleanup();
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_DEFAULT_MQTT_TIMEOUT_MS, _AwsIotProvisioningMqttTimeoutMs );

    /* Test provisioning initialization with mutex creation failures. */
    for( i = 0; ; i++ )
    {
        UnityMalloc_MakeMallocFailAfterCount( i );

        status = AwsIotProvisioning_Init( 0 );

        /* Check that the status is either success or "INIT FAILED". */
        if( status == AWS_IOT_PROVISIONING_SUCCESS )
        {
            break;
        }

        TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_INIT_FAILED, status );

        AwsIotProvisioning_Cleanup();
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Provides code coverage of the Provisioning enum-to-string functions,
 * @ref provisioning_function_strerror.
 */
TEST( Provisioning_Unit_API, StringCoverage )
{
    int32_t i = 0;
    const char * pMessage = NULL;

    /* For each Provisioning Error, check the returned string. */
    while( true )
    {
        pMessage = AwsIotProvisioning_strerror( ( AwsIotProvisioningError_t ) i );
        TEST_ASSERT_NOT_NULL( pMessage );

        if( strncmp( "INVALID STATUS", pMessage, 14 ) == 0 )
        {
            break;
        }

        i++;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies that the API returns the appropriate error code on passing invalid parameters.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPIInvalidParameters )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t callbackInfo =
        AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;

    /* Uninitialized MQTT connection. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( NULL,
                                                          0,
                                                          0,
                                                          NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Unknown Security Setting. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( _pMqttConnection,
                                                          2,
                                                          0,
                                                          &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Callback object is not set. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( _pMqttConnection,
                                                          0,
                                                          0,
                                                          NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Callback function not set. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( _pMqttConnection,
                                                          0,
                                                          0,
                                                          &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies that the API returns the expected error code when it is called without initializing the library.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPICalledWithoutInit )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t callbackInfo =
        AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyKeysAndCertificateCallback;

    /* Reset the library to simulate the test case when the library is not initialized. */
    AwsIotProvisioning_Cleanup();

    /* Call the API under test. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( _pMqttConnection,
                                                          0,
                                                          _testProvisioningApiTimeoutMs,
                                                          &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_NOT_INITIALIZED, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate in case of
 * receiving no response from the server.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPINoServerResponse )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t callbackInfo =
        AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyKeysAndCertificateCallback;

    /* We will not simulate any server response for the timeout to occur! */

    /* Call the API under test. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( _pMqttConnection,
                                                          0,
                                                          _testProvisioningApiTimeoutMs,
                                                          &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_TIMEOUT, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate when Provisioning server rejects the
 * request by publishing on the "/rejected" topic.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPIRejectedResponse )
{
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t callbackInfo =
        AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyKeysAndCertificateCallback;

    _serverResponseThreadContext_t rejectedResponse =
    {
        .pPublishTopic      = _createKeysAndCertificateRejectedResponseTopic,
        .publishTopicLength = strlen( _createKeysAndCertificateRejectedResponseTopic ),
        .pPublishData       = _sampleRejectedServerResponsePayload,
        .publishDataLength  = sizeof( _sampleRejectedServerResponsePayload )
    };

    _testCreateKeysAndCertificateAPIWithServerResponse( &rejectedResponse,
                                                        _testProvisioningServerResponseThreadTimeoutMs,
                                                        &callbackInfo,
                                                        AWS_IOT_PROVISIONING_SERVER_REFUSED );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate when the "accepted" response sent by
 * the AWS IoT Core service contains a corrupt payload.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPICorruptDataInResponse )
{
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t callbackInfo =
        AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyKeysAndCertificateCallback;

    /*************** Response payload without certificate entry********************/
    const uint8_t serverResponseWithoutCertificate[] =
    {
        0xA2,                                                       /* # map( 2 ) */
        0x6A,                                                       /* # text( 10 ) */
        /* THERE IS NO ENTRY FOR "CertificatePem"!! */
        0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65, 0x4B, 0x65, 0x79, /* # "privateKey" */
        0x4A,                                                       /* # bytes( 10 ) */
        0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, /* # "x\x9Ax\x9Ax\x9Ax\x9Ax\x9A" */
    };

    _serverResponseThreadContext_t responseWithoutCertificate =
    {
        .pPublishTopic      = _createKeysAndCertificateAcceptedResponseTopic,
        .publishTopicLength = strlen( _createKeysAndCertificateAcceptedResponseTopic ),
        .pPublishData       = serverResponseWithoutCertificate,
        .publishDataLength  = sizeof( serverResponseWithoutCertificate )
    };

    _testCreateKeysAndCertificateAPIWithServerResponse( &responseWithoutCertificate,
                                                        _testProvisioningServerResponseThreadTimeoutMs,
                                                        &callbackInfo,
                                                        AWS_IOT_PROVISIONING_BAD_RESPONSE );

    /*************** Response payload without private key entry********************/
    const uint8_t serverResponseWithCorruptPrivateKeyEntry[] =
    {
        0xA2,                                                                               /* # map( 2 ) */
        0x6E,                                                                               /* # text( 14 ) */
        0x63, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x50, 0x65, 0x6D, /* # "certificatePem" */
        0x4A,                                                                               /* # bytes( 10 ) */
        0x12, 0x34, 0x12, 0x34, 0x12, 0x34, 0x12, 0x34, 0x12, 0x34,                         /* #
                                                                                             * "\x124\x124\x124\x124\x124"
                                                                                             * */
        0x6A,                                                                               /* # text( 10 ) */
        0x50, 0x75, 0x62, 0x6C, 0x69, 0x63, 0x4B, 0x65, 0x79,                               /* # "PublicKey"  <------
                                                                                             * THIS IS CORRUPT! */
        0x4A,                                                                               /* # bytes( 10 ) */
        0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A, 0x78, 0x9A,                         /* #
                                                                                             * "x\x9Ax\x9Ax\x9Ax\x9Ax\x9A"
                                                                                             * */
    };

    _serverResponseThreadContext_t responseWithoutPrivateKey =
    {
        .pPublishTopic      = _createKeysAndCertificateAcceptedResponseTopic,
        .publishTopicLength = strlen( _createKeysAndCertificateAcceptedResponseTopic ),
        .pPublishData       = serverResponseWithCorruptPrivateKeyEntry,
        .publishDataLength  = sizeof( serverResponseWithCorruptPrivateKeyEntry )
    };

    _testCreateKeysAndCertificateAPIWithServerResponse( &responseWithoutPrivateKey,
                                                        _testProvisioningServerResponseThreadTimeoutMs,
                                                        &callbackInfo,
                                                        AWS_IOT_PROVISIONING_BAD_RESPONSE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate in the nominal case when
 * the server responds correctly on the "accepted" topic.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPINominalSuccess )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _createKeysAndCertificateAcceptedResponseTopic,
        .publishTopicLength = strlen( _createKeysAndCertificateAcceptedResponseTopic ),
        .pPublishData       = _sampleCreateKeysAndCertificateServerResponsePayload,
        .publishDataLength  = sizeof( _sampleCreateKeysAndCertificateServerResponsePayload )
    };

    _testCreateKeysAndCertificateAPIWithServerResponse( &serverResponse,
                                                        _testProvisioningServerResponseThreadTimeoutMs,
                                                        &_acceptedResponseCallbackForCreateKeysAndCertificateAPI,
                                                        AWS_IOT_PROVISIONING_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate when server responds much after the
 * timeout period.
 */
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPIServerResponseAfterTimeout )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _createKeysAndCertificateAcceptedResponseTopic,
        .publishTopicLength = strlen( _createKeysAndCertificateAcceptedResponseTopic ),
        .pPublishData       = _sampleCreateKeysAndCertificateServerResponsePayload,
        .publishDataLength  = sizeof( _sampleCreateKeysAndCertificateServerResponsePayload )
    };

    _testCreateKeysAndCertificateAPIWithServerResponse( &serverResponse,
                                                        _testProvisioningServerResponseThreadTimeoutMs * 2,
                                                        &_acceptedResponseCallbackForCreateKeysAndCertificateAPI,
                                                        AWS_IOT_PROVISIONING_TIMEOUT );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate when there is a race condition between
 * the library receiving the server response and the response timeout firing. Even in such a case, the API is expected
 * to process the response and invoke the user callback with the device credentials instead of treating the case as a
 * timeout!*/
TEST( Provisioning_Unit_API, CreateKeysAndCertificateAPIServerResponseAndTimeoutRaceCondition )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _createKeysAndCertificateAcceptedResponseTopic,
        .publishTopicLength = strlen( _createKeysAndCertificateAcceptedResponseTopic ),
        .pPublishData       = _sampleCreateKeysAndCertificateServerResponsePayload,
        .publishDataLength  = sizeof( _sampleCreateKeysAndCertificateServerResponsePayload )
    };

    _testCreateKeysAndCertificateAPIWithServerResponse( &serverResponse,
                                                        _testProvisioningApiTimeoutMs,
                                                        &_acceptedResponseCallbackForCreateKeysAndCertificateAPI,
                                                        AWS_IOT_PROVISIONING_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests that the API detects invalid parameters passed to it, and returns the
 * equivalent error code.
 */
TEST( Provisioning_Unit_API, RegisterThingAPIInvalidParameters )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo =
        AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyRegisterThingCallback;

    AwsIotProvisioningRegisterThingRequestInfo_t requestInfo =
    {
        .pDeviceCertificateId       = _testCertificateId,
        .deviceCertificateIdLength  = strlen( _testCertificateId ),
        .pCertificateOwnershipToken = _testCertificateToken,
        .ownershipTokenLength       = strlen( _testCertificateToken ),
        .pTemplateName              = _testTemplateName,
        .templateNameLength         = strlen( _testTemplateName ),
        .pParametersStart           = NULL,
        .numOfParameters            = 0,
    };

    /* Uninitialized MQTT connection. */
    status = AwsIotProvisioning_RegisterThing( NULL,
                                               &requestInfo,
                                               0,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Callback object is not set. */
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               0,
                                               NULL );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Callback function not set. */
    callbackInfo.function = NULL;
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               0,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Invalid request data. */
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               NULL,
                                               0,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    /* Invalid certificate data in request data. */
    requestInfo.pDeviceCertificateId = NULL;
    requestInfo.deviceCertificateIdLength = 0;
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               0,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    requestInfo.pDeviceCertificateId = _testCertificateId;
    requestInfo.deviceCertificateIdLength = sizeof( _testCertificateId );

    /* Invalid certificate token string in request. */
    requestInfo.pCertificateOwnershipToken = NULL;
    requestInfo.ownershipTokenLength = 0;
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               0,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );

    requestInfo.ownershipTokenLength = strlen( _testCertificateToken );
    requestInfo.pTemplateName = _testTemplateName;

    /* Invalid template ID in request data. Re-assign certificate data in object. */
    requestInfo.pTemplateName = NULL;
    requestInfo.templateNameLength = 0;
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               0,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_BAD_PARAMETER, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies that the API returns the expected error code when it is called without initializing the library.
 */
TEST( Provisioning_Unit_API, RegisterThingAPICalledWithoutInit )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo = AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyRegisterThingCallback;

    const AwsIotProvisioningRegisterThingRequestInfo_t requestInfo =
    {
        .pDeviceCertificateId       = _testCertificateId,
        .deviceCertificateIdLength  = sizeof( _testCertificateId ),
        .pCertificateOwnershipToken = _testCertificateToken,
        .ownershipTokenLength       = strlen( _testCertificateToken ),
        .pTemplateName              = _testTemplateName,
        .templateNameLength         = strlen( _testTemplateName ),
        .pParametersStart           = NULL,
        .numOfParameters            = 0,
    };

    /* Reset the library to simulate the test case when the library is not initialized. */
    AwsIotProvisioning_Cleanup();

    /* Call the API under test. */
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               _testProvisioningApiTimeoutMs,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_NOT_INITIALIZED, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_getpKeysAndCertificate in case of
 * receiving no response from the server.
 */
TEST( Provisioning_Unit_API, RegisterThingAPINoServerResponse )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _dummyRegisterThingCallback
    };

    const AwsIotProvisioningRegisterThingRequestInfo_t requestInfo =
    {
        .pDeviceCertificateId       = _testCertificateId,
        .deviceCertificateIdLength  = sizeof( _testCertificateId ),
        .pTemplateName              = _testTemplateName,
        .templateNameLength         = strlen( _testTemplateName ),
        .pCertificateOwnershipToken = _testCertificateToken,
        .ownershipTokenLength       = strlen( _testCertificateToken ),
        .pParametersStart           = NULL,
        .numOfParameters            = 0,
    };


    /* We will not simulate any server response for the timeout to occur! */

    /* Call the API under test. */
    status = AwsIotProvisioning_RegisterThing( _pMqttConnection,
                                               &requestInfo,
                                               _testProvisioningApiTimeoutMs,
                                               &callbackInfo );
    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_TIMEOUT, status );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing when Provisioning server rejects the request
 * by publishing on the "/rejected" topic.
 */
TEST( Provisioning_Unit_API, RegisterThingAPIRejectedResponse )
{
    AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo = AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyRegisterThingCallback;

    _serverResponseThreadContext_t rejectedResponse =
    {
        .pPublishTopic      = _registerThingRejectedResponseTopic,
        .publishTopicLength = strlen( _registerThingRejectedResponseTopic ),
        .pPublishData       = _sampleRejectedServerResponsePayload,
        .publishDataLength  = sizeof( _sampleRejectedServerResponsePayload )
    };

    _testRegisterThingAPIWithServerResponse( &rejectedResponse,
                                             _testProvisioningServerResponseThreadTimeoutMs,
                                             &callbackInfo,
                                             AWS_IOT_PROVISIONING_SERVER_REFUSED );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing API when the "accepted" response sent by the
 * AWS IoT Core service contains a corrupt payload.
 */
TEST( Provisioning_Unit_API, RegisterThingAPICorruptDataInResponse )
{
    AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo = AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;

    callbackInfo.function = _dummyRegisterThingCallback;

    /*************** Response Payload containing invalid device configuration entry ********************/
    const uint8_t serverResponseWithInvalidDeviceConfigEntry[] =
    {
        0xA2,                                                 /* # map(2) */
        0x73,                                                 /* # text(19) */
        0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61,
        0x74, 0x69, 0x6F, 0x6E,                               /* # "deviceConfiguration" */
        0x82,                                                 /* # array(2) */
        0x01,                                                 /* # unsigned(1) */
        0x02,                                                 /* # unsigned(2) */
        0x69,                                                 /* # text(9) */
        0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
        0x69,                                                 /* # text(9) */
        0x54, 0x65, 0x73, 0x74, 0x54, 0x68, 0x69, 0x6E, 0x67  /* # "TestThing" */
    };

    _serverResponseThreadContext_t corruptResponseContext =
    {
        .pPublishTopic      = _registerThingAcceptedResponseTopic,
        .publishTopicLength = strlen( _registerThingAcceptedResponseTopic ),
        .pPublishData       = serverResponseWithInvalidDeviceConfigEntry,
        .publishDataLength  = sizeof( serverResponseWithInvalidDeviceConfigEntry )
    };

    _testRegisterThingAPIWithServerResponse( &corruptResponseContext,
                                             _testProvisioningServerResponseThreadTimeoutMs,
                                             &callbackInfo,
                                             AWS_IOT_PROVISIONING_BAD_RESPONSE );

    /***************  Response Payload with invalid Thing Name entry ********************/
    const uint8_t serverResponseWithInvalidThingNameEntry[] =
    {
        0xA2,                                                 /* # map(2) */
        0x73,                                                 /* # text(19) */
        0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61,
        0x74, 0x69, 0x6F, 0x6E,                               /* # "deviceConfiguration" */
        0xA1,                                                 /* # map(1), */
        0x61,                                                 /* # text(1), */
        0x31,                                                 /* # "1", */
        0x02,                                                 /* # unsigned(2), */
        0x69,                                                 /* # text(9) */
        0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
        0x04                                                  /* # unsigned(4) */
    };

    corruptResponseContext.pPublishData = serverResponseWithInvalidThingNameEntry;
    corruptResponseContext.publishDataLength = sizeof( serverResponseWithInvalidThingNameEntry );

    _testRegisterThingAPIWithServerResponse( &corruptResponseContext,
                                             _testProvisioningServerResponseThreadTimeoutMs,
                                             &callbackInfo,
                                             AWS_IOT_PROVISIONING_BAD_RESPONSE );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing in the nominal case when
 * the server responds correctly on the "accepted" topic.
 */
TEST( Provisioning_Unit_API, RegisterThingAPINominalSuccess )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _registerThingAcceptedResponseTopic,
        .publishTopicLength = strlen( _registerThingAcceptedResponseTopic ),
        .pPublishData       = _sampleRegisterThingResponsePayload,
        .publishDataLength  = sizeof( _sampleRegisterThingResponsePayload )
    };

    _testRegisterThingAPIWithServerResponse( &serverResponse,
                                             _testProvisioningServerResponseThreadTimeoutMs,
                                             &_acceptedResponseCallbackForRegisterThingAPI,
                                             AWS_IOT_PROVISIONING_SUCCESS );
}
/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing in the case when
 * the server responds on the "accepted" topic but without any device configuration data in the payload.
 */
TEST( Provisioning_Unit_API, RegisterThingAPIServerResponseWithoutDeviceConfiguration )
{
    const uint8_t pResponseWithoutDeviceConfigData[] =
    {
        0xA1,                                                 /* # map(1) */
        0x69,                                                 /* # text(9) */
        0x74, 0x68, 0x69, 0x6E, 0x67, 0x4E, 0x61, 0x6D, 0x65, /* # "thingName" */
        0x69,                                                 /* # text(9) */
        0x54, 0x65, 0x73, 0x74, 0x54, 0x68, 0x69, 0x6E, 0x67, /* # "TestThing" */
        0x68,                                                 /* # text(8) */
    };

    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _registerThingAcceptedResponseTopic,
        .publishTopicLength = strlen( _registerThingAcceptedResponseTopic ),
        .pPublishData       = pResponseWithoutDeviceConfigData,
        .publishDataLength  = sizeof( pResponseWithoutDeviceConfigData )
    };

    AwsIotProvisioningRegisterThingResponse_t expectedCallbackParams =
    {
        .statusCode                                   = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED,
        .u.acceptedResponse.pThingName                = ( const char * ) &pResponseWithoutDeviceConfigData[ 12 ],
        .u.acceptedResponse.thingNameLength           = 9,
        .u.acceptedResponse.pDeviceConfigList         = NULL,
        .u.acceptedResponse.numOfConfigurationEntries = 0
    };

    const AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo =
    {
        .userParam = &expectedCallbackParams,
        .function  = _testRegisterThingCallback
    };


    _testRegisterThingAPIWithServerResponse( &serverResponse,
                                             _testProvisioningServerResponseThreadTimeoutMs,
                                             &callbackInfo,
                                             AWS_IOT_PROVISIONING_SUCCESS );
}

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing in the case when
 * the server responds on the "accepted" topic but without thing name entry in the payload.
 */
TEST( Provisioning_Unit_API, RegisterThingAPIServerResponseWithoutThingName )
{
    const uint8_t pServerResponseWithoutThingName[] =
    {
        0xA1,                   /* # map(1) */
        0x73,                   /* # text(19) */
        0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x43, 0x6F, 0x6E, 0x66, 0x69, 0x67, 0x75, 0x72, 0x61,
        0x74, 0x69, 0x6F, 0x6E, /* # "deviceConfiguration" */
        0xA1,                   /* # map(1), */
        0x61,                   /* # text(1), */
        0x31,                   /* # "1", */
        0x61,                   /* # text(1), */
        0x32,                   /* # "2" */
        0x68,                   /*# text(8) */
    };

    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _registerThingAcceptedResponseTopic,
        .publishTopicLength = strlen( _registerThingAcceptedResponseTopic ),
        .pPublishData       = pServerResponseWithoutThingName,
        .publishDataLength  = sizeof( pServerResponseWithoutThingName )
    };

    const AwsIotProvisioningResponseDeviceConfigurationEntry_t pExpectedDeviceConfigList[] =
    {
        {
            ( const char * ) &pServerResponseWithoutThingName[ 23 ],
            1,
            ( const char * ) &pServerResponseWithoutThingName[ 25 ],
            1
        }
    };

    AwsIotProvisioningRegisterThingResponse_t expectedCallbackParams =
    {
        .statusCode                                   = AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED,
        .u.acceptedResponse.pThingName                = NULL,
        .u.acceptedResponse.thingNameLength           = 0,
        .u.acceptedResponse.pDeviceConfigList         = pExpectedDeviceConfigList,
        .u.acceptedResponse.numOfConfigurationEntries = 1
    };

    const AwsIotProvisioningRegisterThingCallbackInfo_t callbackInfo =
    {
        .userParam = &expectedCallbackParams,
        .function  = _testRegisterThingCallback
    };

    _testRegisterThingAPIWithServerResponse( &serverResponse,
                                             _testProvisioningServerResponseThreadTimeoutMs,
                                             &callbackInfo,
                                             AWS_IOT_PROVISIONING_SUCCESS );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing when server responds much after the timeout
 * period.
 */
TEST( Provisioning_Unit_API, RegisterThingAPIServerResponseAfterTimeout )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _registerThingAcceptedResponseTopic,
        .publishTopicLength = strlen( _registerThingAcceptedResponseTopic ),
        .pPublishData       = _sampleRegisterThingResponsePayload,
        .publishDataLength  = sizeof( _sampleRegisterThingResponsePayload )
    };

    _testRegisterThingAPIWithServerResponse( &serverResponse,
                                             _testProvisioningServerResponseThreadTimeoutMs * 2,
                                             &_acceptedResponseCallbackForRegisterThingAPI,
                                             AWS_IOT_PROVISIONING_TIMEOUT );
}

/*-----------------------------------------------------------*/

/**
 * @brief Tests the behavior of @ref provisioning_function_registerthing when there is a race condition between
 * the library receiving the server response and the response timeout firing. Even in such a case, the API is expected
 * to process the response and invoke the user callback with the device credentials instead of treating the case as a
 * timeout!*/
TEST( Provisioning_Unit_API, RegisterThingAPIServerResponseAndTimeoutRaceCondition )
{
    _serverResponseThreadContext_t serverResponse =
    {
        .pPublishTopic      = _registerThingAcceptedResponseTopic,
        .publishTopicLength = strlen( _registerThingAcceptedResponseTopic ),
        .pPublishData       = _sampleRegisterThingResponsePayload,
        .publishDataLength  = sizeof( _sampleRegisterThingResponsePayload )
    };

    _testRegisterThingAPIWithServerResponse( &serverResponse,
                                             _testProvisioningApiTimeoutMs,
                                             &_acceptedResponseCallbackForRegisterThingAPI,
                                             AWS_IOT_PROVISIONING_SUCCESS );
}
