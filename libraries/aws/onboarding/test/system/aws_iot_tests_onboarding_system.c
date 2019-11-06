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
 * @file aws_iot_tests_onboarding_system.c
 * @brief Full system tests for the AWS IoT Onboarding library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* SDK initialization include. */
#include "iot_init.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Onboarding include. */
#include "private/aws_iot_onboarding_internal.h"

/* Test network header include. */
#include IOT_TEST_NETWORK_HEADER

/* Test framework includes. */
#include "unity_fixture.h"

/* JSON utilities include. */
#include "iot_json_utils.h"

/* Logging Include */
#include "iot_logging_setup.h"

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values of test configuration constants.
 */
#ifndef AWS_IOT_TEST_ONBOARDING_TIMEOUT
    #define AWS_IOT_TEST_ONBOARDING_TIMEOUT    ( 60000 )
#endif
/** @endcond */

/* Require ONBOARDING library asserts to be enabled for these tests. The ONBOARDING
 * assert function is used to abort the tests on failure from the ONBOARDING operation
 * complete callback. */
#if AWS_IOT_ONBOARDING_ENABLE_ASSERTS == 0
    #error "ONBOARDING system tests require AWS_IOT_ONBOARDING_ENABLE_ASSERTS to be 1."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Network server info to share among the tests.
 */
static const IotTestNetworkServerInfo_t _serverInfo = IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER;

/**
 * @brief Network credential info to share among the tests.
 */
#if IOT_TEST_SECURED_CONNECTION == 1
    static const IotTestNetworkCredentials_t _credentials =
        IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER;
#endif

/**
 * @brief An MQTT network setup parameter to share among the tests.
 */
static IotMqttNetworkInfo_t _networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;

/**
 * @brief An MQTT connection to share among the tests.
 */
static IotMqttConnection_t _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

/**
 * @brief Client ID for the MQTT connection to the Onboarding service.
 */
static const char * _pTestMqttClientId = "onnboarding-system-test";

/**
 * @brief Certificate ID for OnboardDevice API tests.
 */
static char * _testCertificateId = "1c163fd8fcac4a7dc1da34744b6e7c994664c1d399c356d0fce400027d6e45e4";

static const AwsIotOnboardingRequestParameterEntry_t _pTestParameters[] =
    AWS_IOT_TEST_ONBOARDING_TEMPLATE_PARAMETERS;

/*-----------------------------------------------------------*/

/**
 * @brief Verifies the validity of the parsed "rejected" response data and prints the data.
 */
static void _printRejectedResponse( const AwsIotOnboardingRejectedResponse_t * pResponseInfo )
{
    AwsIotOnboarding_Assert( pResponseInfo != NULL );

    IotLogError( "\n Request REJECTED!!\n ErrorCode={%.*s}\n ErrorMessage={%.*s}\n",
                 pResponseInfo->errorCodeLength, pResponseInfo->pErrorCode,
                 pResponseInfo->errorMessageLength, pResponseInfo->pErrorMessage );
}

/*-----------------------------------------------------------*/

/**
 * @brief User callback function for printing parsed response data sent by the GetDeviceCredentials service API.
 */
static void _printDeviceCredentialsCallback( void * contextParam,
                                             const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    AwsIotOnboarding_Assert( pResponseInfo != NULL );

    IotLogInfo( "\n Status Code = %d\n", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_ONBOARDING_SERVER_STATUS_ACCEPTED )
    {
        /* Check parameters against expected values. */
        TEST_ASSERT_NOT_NULL( pResponseInfo->u.acceptedResponse.pDeviceCertificate );
        TEST_ASSERT_GREATER_THAN( 0, pResponseInfo->u.acceptedResponse.deviceCertificateLength );
        TEST_ASSERT_NOT_NULL( pResponseInfo->u.acceptedResponse.pPrivateKey );
        TEST_ASSERT_GREATER_THAN( 0, pResponseInfo->u.acceptedResponse.privateKeyLength );

        IotLogInfo( "\n Certificate PEM = %.*s\n Certificate ID = %.*s\n DREADED PRIVATE KEY = %.*s\n",
                    pResponseInfo->u.acceptedResponse.deviceCertificateLength,
                    pResponseInfo->u.acceptedResponse.pDeviceCertificate,
                    pResponseInfo->u.acceptedResponse.certificateIdLength,
                    pResponseInfo->u.acceptedResponse.pCertificateId,
                    pResponseInfo->u.acceptedResponse.privateKeyLength,
                    pResponseInfo->u.acceptedResponse.pPrivateKey );
    }
    else
    {
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief User callback function for printing parsed response data sent by the OnboardDevice service API.
 */
static void _printOnboardDeviceResponseCallback( void * contextParam,
                                                 const AwsIotOnboardingOnboardDeviceResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    AwsIotOnboarding_Assert( pResponseInfo != NULL );

    IotLogInfo( "\n Status Code = %d\n", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_ONBOARDING_SERVER_STATUS_ACCEPTED )
    {
        if( pResponseInfo->u.acceptedResponse.pThingName != NULL )
        {
            if( pResponseInfo->u.acceptedResponse.pThingName != NULL )
            {
                IotLogInfo( "ThingName = %.*s",
                            pResponseInfo->u.acceptedResponse.thingNameLength,
                            pResponseInfo->u.acceptedResponse.pThingName );
            }
        }

        if( pResponseInfo->u.acceptedResponse.numOfConfigurationEntries > 0 )
        {
            const AwsIotOnboardingResponseDeviceConfigurationEntry_t * pConfigurationList =
                pResponseInfo->u.acceptedResponse.pDeviceConfigList;

            for( size_t configIndex = 0;
                 configIndex < pResponseInfo->u.acceptedResponse.numOfConfigurationEntries;
                 configIndex++ )
            {
                IotLogInfo( "Device Configuration no. %d:ConfigName = %.*s, ConfigData = %.*s ",
                            configIndex,
                            pConfigurationList[ configIndex ].keyLength,
                            pConfigurationList[ configIndex ].pKey,
                            pConfigurationList[ configIndex ].valueLength,
                            pConfigurationList[ configIndex ].pValue );
            }
        }
    }
    else
    {
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group for Onboarding system tests.
 */
TEST_GROUP( Onboarding_System );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Onboarding system tests.
 */
TEST_SETUP( Onboarding_System )
{
    static uint64_t lastConnectTime = 0;
    uint64_t elapsedTime = 0;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    /* Initialize SDK. */
    if( IotSdk_Init() == false )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize SDK." );
    }

    /* Set up the network stack. */
    if( IotTestNetwork_Init() != IOT_NETWORK_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to set up network stack." );
    }

    /* Initialize the MQTT library. */
    if( IotMqtt_Init() != IOT_MQTT_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize MQTT library." );
    }

    /* Initialize the Onboarding library. */
    if( AwsIotOnboarding_Init( 0 ) != AWS_IOT_ONBOARDING_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize Onboarding library." );
    }

    /* Set the MQTT network setup parameters. */
    ( void ) memset( &_networkInfo, 0x00, sizeof( IotMqttNetworkInfo_t ) );
    _networkInfo.createNetworkConnection = true;
    _networkInfo.u.setup.pNetworkServerInfo = ( void * ) &_serverInfo;
    _networkInfo.pNetworkInterface = IOT_TEST_NETWORK_INTERFACE;

    #if IOT_TEST_SECURED_CONNECTION == 1
        _networkInfo.u.setup.pNetworkCredentialInfo = ( void * ) &_credentials;
    #endif

    #ifdef IOT_TEST_MQTT_SERIALIZER
        _networkInfo.pMqttSerializer = IOT_TEST_MQTT_SERIALIZER;
    #endif

    /* Set the members of the connect info. Use the Onboarding Thing Name as the MQTT
     * client identifier. */
    connectInfo.awsIotMqttMode = true;
    connectInfo.pClientIdentifier = _pTestMqttClientId;
    connectInfo.clientIdentifierLength = strlen( _pTestMqttClientId );
    connectInfo.keepAliveSeconds = AWS_IOT_TEST_ONBOARDING_TIMEOUT;

    /* AWS IoT Service limits only allow 1 connection per MQTT client ID per second.
     * Wait until 1100 ms have elapsed since the last connection. */
    elapsedTime = IotClock_GetTimeMs() - lastConnectTime;

    if( elapsedTime < 1100ULL )
    {
        IotClock_SleepMs( 1100UL - ( uint32_t ) elapsedTime );
    }

    /* Establish an MQTT connection. */
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    status = IotMqtt_Connect( &_networkInfo,
                              &connectInfo,
                              AWS_IOT_TEST_ONBOARDING_TIMEOUT,
                              &_mqttConnection );

    if( status != IOT_MQTT_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to establish MQTT connection for Onboarding tests" );
    }

    /* Update the time of the last MQTT connect. */
    lastConnectTime = IotClock_GetTimeMs();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Onboarding system tests.
 */
TEST_TEAR_DOWN( Onboarding_System )
{
    /* Disconnect the MQTT connection if it was created. */
    if( _mqttConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotMqtt_Disconnect( _mqttConnection, 0 );
        _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    }

    AwsIotOnboarding_Cleanup();

    /* Clean up the MQTT library. */
    IotMqtt_Cleanup();

    /* Clean up the network stack. */
    IotTestNetwork_Cleanup();

    /* Clean up SDK. */
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Onboarding system tests.
 */
TEST_GROUP_RUNNER( Onboarding_System )
{
    /*RUN_TEST_CASE( Onboarding_System, GetDeviceCredentialsNominalCase ); */
    RUN_TEST_CASE( Onboarding_System, OnboardDeviceNominalCase );
}

/*-----------------------------------------------------------*/


/**
 * @brief Tests the behavior of the GetDeviceCredentials API in the nominal (or success) case where the server responds
 * within the specified timeout period.
 */
TEST( Onboarding_System, GetDeviceCredentialsNominalCase )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;
    AwsIotOnboardingGetDeviceCredentialsCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _printDeviceCredentialsCallback
    };

    status = AwsIotOnboarding_GetDeviceCredentials( _mqttConnection,
                                                    0,
                                                    AWS_IOT_TEST_ONBOARDING_TIMEOUT,
                                                    &callbackInfo );

    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS, status );
}

/**
 * @brief Tests the behavior of the OnboardDevice API in the nominal (or success) case where the server responds
 * within the specified timeout period.
 */
TEST( Onboarding_System, OnboardDeviceNominalCase )
{
    AwsIotOnboardingError_t status = AWS_IOT_ONBOARDING_SUCCESS;

    AwsIotOnboardingOnboardDeviceCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _printOnboardDeviceResponseCallback
    };

    AwsIotOnboardingOnboardDeviceRequestInfo_t requestInfo;

    requestInfo.pDeviceCertificateId = _testCertificateId;
    requestInfo.deviceCertificateIdLength = strlen( _testCertificateId );
    requestInfo.pTemplateIdentifier = AWS_IOT_TEST_ONBOARDING_TEMPLATE_NAME;
    requestInfo.templateIdentifierLength = ( sizeof( AWS_IOT_TEST_ONBOARDING_TEMPLATE_NAME ) - 1 );
    requestInfo.pParametersStart = _pTestParameters;
    requestInfo.numOfParameters = sizeof( _pTestParameters ) /
                                  sizeof( AwsIotOnboardingRequestParameterEntry_t );

    /* Call the API under test. */
    status = AwsIotOnboarding_OnboardDevice( _mqttConnection,
                                             &requestInfo,
                                             AWS_IOT_TEST_ONBOARDING_TIMEOUT,
                                             &callbackInfo );


    TEST_ASSERT_EQUAL( AWS_IOT_ONBOARDING_SUCCESS, status );
}
