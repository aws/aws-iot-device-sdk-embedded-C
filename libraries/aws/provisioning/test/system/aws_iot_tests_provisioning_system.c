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
 * @file aws_iot_tests_provisioning_system.c
 * @brief Full system tests for the AWS IoT Provisioning library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* SDK initialization include. */
#include "iot_init.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Provisioning include. */
#include "private/aws_iot_provisioning_internal.h"

/* Test network header include. */
#include IOT_TEST_NETWORK_HEADER

/* Test framework includes. */
#include "unity_fixture.h"

/* Logging Include */
#include "iot_logging_setup.h"

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values of test configuration constants.
 */
#ifndef AWS_IOT_TEST_PROVISIONING_TIMEOUT
    #define AWS_IOT_TEST_PROVISIONING_TIMEOUT    ( 60000 )
#endif
/** @endcond */

/* Require PROVISIONING library asserts to be enabled for these tests. The PROVISIONING
 * assert function is used to abort the tests on failure from the PROVISIONING operation
 * complete callback. */
#if AWS_IOT_PROVISIONING_ENABLE_ASSERTS == 0
    #error "PROVISIONING system tests require AWS_IOT_PROVISIONING_ENABLE_ASSERTS to be 1."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Network server info to share among the tests.
 */
static const struct IotNetworkServerInfo _serverInfo =
    IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER;

/**
 * @brief Network credential info to share among the tests.
 */
#if IOT_TEST_SECURED_CONNECTION == 1
    static const struct IotNetworkCredentials _credentials =
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
 * @brief Client ID for the MQTT connection to the AWS IoT Core service.
 */
static const char * _pTestMqttClientId = "SystemTestClientID";

/**
 * @brief Parameters to use for testing the Provisioning RegisterThing API.
 */
static const AwsIotProvisioningRequestParameterEntry_t _pTestParameters[] =
    AWS_IOT_TEST_PROVISIONING_TEMPLATE_PARAMETERS;

/**
 * @brief Type for the context parameter for the certificate-creation API callbacks.
 *
 * It will be used for storing the received Certificate ID and the ownership token
 * data received from the server. These can then be used for the RegisterThing API test.
 */
typedef struct _certIdAndOwnershipTokenContext
{
    char * pCertificateIdBuffer;
    size_t certificateIdLength;
    char * pCertificateOwnershipToken;
    size_t tokenLength;
} _certIdAndOwnershipTokenContext_t;

/*-----------------------------------------------------------*/

/**
 * @brief Verifies the validity of the parsed "rejected" response data and prints the data.
 */
static void _printRejectedResponse( const AwsIotProvisioningRejectedResponse_t * pResponseInfo )
{
    /*Disable unused parameter warning. */
    ( void ) pResponseInfo;

    TEST_ASSERT_NOT_NULL( pResponseInfo );

    IotLogError( "\n Request REJECTED!!\n ErrorCode={%.*s}\n ErrorMessage={%.*s}\n",
                 pResponseInfo->errorCodeLength, pResponseInfo->pErrorCode,
                 pResponseInfo->errorMessageLength, pResponseInfo->pErrorMessage );
}

/*-----------------------------------------------------------*/

/**
 * @brief User callback function for printing parsed response data sent by the Provisioning CreateKeysAndCertificate
 * service API.
 */
static void _printKeysAndCertificateCallback( void * contextParam,
                                              const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    TEST_ASSERT_NOT_NULL( pResponseInfo );

    IotLogInfo( "\n Status Code = %d\n", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        /* Check parameters against expected values. */
        TEST_ASSERT_NOT_NULL( pResponseInfo->u.acceptedResponse.pDeviceCertificate );
        TEST_ASSERT_GREATER_THAN( 0, pResponseInfo->u.acceptedResponse.deviceCertificateLength );
        TEST_ASSERT_NOT_NULL( pResponseInfo->u.acceptedResponse.pPrivateKey );
        TEST_ASSERT_GREATER_THAN( 0, pResponseInfo->u.acceptedResponse.privateKeyLength );

        IotLogInfo( "\n Certificate PEM = %.*s\n Certificate ID = %.*s\n Ownership Token = %.*s\n DREADED PRIVATE KEY = %.*s\n",
                    pResponseInfo->u.acceptedResponse.deviceCertificateLength,
                    pResponseInfo->u.acceptedResponse.pDeviceCertificate,
                    pResponseInfo->u.acceptedResponse.certificateIdLength,
                    pResponseInfo->u.acceptedResponse.pCertificateId,
                    pResponseInfo->u.acceptedResponse.ownershipTokenLength,
                    pResponseInfo->u.acceptedResponse.pCertificateOwnershipToken,
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
 * @brief User callback function for printing parsed response data from the
 * MQTT CreateCertificateFromCsr service API.
 */
static void _printCertificateFromCsrCallback( void * contextParam,
                                              const AwsIotProvisioningCreateCertFromCsrResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    TEST_ASSERT_NOT_NULL( pResponseInfo );

    IotLogInfo( "\n Status Code = %d\n", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        /* Check parameters against expected values. */
        TEST_ASSERT_NOT_NULL( pResponseInfo->u.acceptedResponse.pDeviceCert );
        TEST_ASSERT_GREATER_THAN( 0, pResponseInfo->u.acceptedResponse.deviceCertLength );

        IotLogInfo( "\n Certificate PEM = %.*s\n Certificate ID = %.*s\n Ownership Token = %.*s\n",
                    pResponseInfo->u.acceptedResponse.deviceCertLength,
                    pResponseInfo->u.acceptedResponse.pDeviceCert,
                    pResponseInfo->u.acceptedResponse.certIdLength,
                    pResponseInfo->u.acceptedResponse.pCertId,
                    pResponseInfo->u.acceptedResponse.ownershipTokenLength,
                    pResponseInfo->u.acceptedResponse.pCertOwnershipToken );
    }
    else
    {
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback function that tests for the "Invalid CSR" status in the
 * parsed server response in the failure case of calling of the CreateCertFromCsr API
 * with an invalid CSR string.
 */
static void _checkInvalidCsrServerResponseCallback( void * contextParam,
                                                    const AwsIotProvisioningCreateCertFromCsrResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    TEST_ASSERT_NOT_NULL( pResponseInfo );

    /* Make sure that we have received an "Invalid CSR" response from the server. */
    TEST_ASSERT_MESSAGE( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_INVALID_CSR,
                         "Callback didn't receive the expected rejected server response status: "
                         "ExpectedResponseStatus={INVALID_CSR}" );

    _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for the KeysAndCertificate operation for copying the server provided
 * credentials in buffers for use in RegisterThing test.
 */
static void _storeDataFromKeysAndCertResponseCallback( void * contextParam,
                                                       const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    _certIdAndOwnershipTokenContext_t * certificateIdTokenContext =
        ( _certIdAndOwnershipTokenContext_t * ) contextParam;

    IotLogInfo( "Received StatusCode={%d}", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        /* Allocate buffer space for storing the certificate ID obtained from the server. */
        certificateIdTokenContext->pCertificateIdBuffer =
            IotTest_Malloc( pResponseInfo->u.acceptedResponse.certificateIdLength + 1 );
        TEST_ASSERT_NOT_NULL( certificateIdTokenContext->pCertificateIdBuffer );

        /* Copy the certificate ID into the buffer. */
        if( certificateIdTokenContext->pCertificateIdBuffer != NULL )
        {
            /* Copy the size of the Certificate ID string. */
            certificateIdTokenContext->certificateIdLength = pResponseInfo->u.acceptedResponse.certificateIdLength;

            memcpy( certificateIdTokenContext->pCertificateIdBuffer,
                    pResponseInfo->u.acceptedResponse.pCertificateId,
                    pResponseInfo->u.acceptedResponse.certificateIdLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( certificateIdTokenContext->pCertificateIdBuffer + pResponseInfo->u.acceptedResponse.certificateIdLength ) = '\0';
        }

        /* Allocate buffer space for storing the ownership token string obtained from the server. */
        certificateIdTokenContext->pCertificateOwnershipToken =
            IotTest_Malloc( pResponseInfo->u.acceptedResponse.ownershipTokenLength + 1 );
        TEST_ASSERT_NOT_NULL( certificateIdTokenContext->pCertificateOwnershipToken );

        /* Copy the ownership token into the buffer. */
        if( certificateIdTokenContext->pCertificateOwnershipToken != NULL )
        {
            /* Copy the size of the ownership token string. */
            certificateIdTokenContext->tokenLength = pResponseInfo->u.acceptedResponse.ownershipTokenLength;

            memcpy( certificateIdTokenContext->pCertificateOwnershipToken,
                    pResponseInfo->u.acceptedResponse.pCertificateOwnershipToken,
                    pResponseInfo->u.acceptedResponse.ownershipTokenLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( certificateIdTokenContext->pCertificateOwnershipToken + pResponseInfo->u.acceptedResponse.ownershipTokenLength ) = '\0';
        }

        /* We don't need the rest of the data for provisioning the test. */
    }
    else
    {
        TEST_FAIL_MESSAGE( "Request for new credentials was rejected! Aborting Test." );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for the CertificateFromCsr operation for copying the server provided
 * credentials in buffers for use in RegisterThing test.
 */
static void _storeDataOfCerFromCsrResponseCallback( void * contextParam,
                                                    const AwsIotProvisioningCreateCertFromCsrResponse_t * pResponseInfo )
{
    _certIdAndOwnershipTokenContext_t * contextData =
        ( _certIdAndOwnershipTokenContext_t * ) contextParam;

    IotLogInfo( "Received StatusCode={%d}", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        /* Allocate buffer space for storing the certificate ID obtained from the server. */
        contextData->pCertificateIdBuffer =
            IotTest_Malloc( pResponseInfo->u.acceptedResponse.certIdLength + 1 );
        TEST_ASSERT_NOT_NULL( contextData->pCertificateIdBuffer );

        /* Copy the certificate ID into the buffer. */
        if( contextData->pCertificateIdBuffer != NULL )
        {
            /* Copy the size of the Certificate ID string. */
            contextData->certificateIdLength = pResponseInfo->u.acceptedResponse.certIdLength;

            memcpy( contextData->pCertificateIdBuffer,
                    pResponseInfo->u.acceptedResponse.pCertId,
                    pResponseInfo->u.acceptedResponse.certIdLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( contextData->pCertificateIdBuffer + pResponseInfo->u.acceptedResponse.certIdLength ) = '\0';
        }

        /* Allocate buffer space for storing the ownership token string obtained from the server. */
        contextData->pCertificateOwnershipToken =
            IotTest_Malloc( pResponseInfo->u.acceptedResponse.ownershipTokenLength + 1 );
        TEST_ASSERT_NOT_NULL( contextData->pCertificateOwnershipToken );

        /* Copy the ownership token into the buffer. */
        if( contextData->pCertificateOwnershipToken != NULL )
        {
            /* Copy the size of the ownership token string. */
            contextData->tokenLength = pResponseInfo->u.acceptedResponse.ownershipTokenLength;

            memcpy( contextData->pCertificateOwnershipToken,
                    pResponseInfo->u.acceptedResponse.pCertOwnershipToken,
                    pResponseInfo->u.acceptedResponse.ownershipTokenLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( contextData->pCertificateOwnershipToken + pResponseInfo->u.acceptedResponse.ownershipTokenLength ) = '\0';
        }

        /* We don't need the rest of the data for provisioning the test. */
    }
    else
    {
        TEST_FAIL_MESSAGE( "Request for new credentials was rejected! Aborting Test." );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief User callback function for printing parsed response data sent by the Provisioning RegisterThing service API.
 */
static void _printRegisterThingResponseCallback( void * contextParam,
                                                 const AwsIotProvisioningRegisterThingResponse_t * pResponseInfo )
{
    ( void ) contextParam;
    TEST_ASSERT_NOT_NULL( pResponseInfo );

    IotLogInfo( "\n Status Code = %d\n", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        if( pResponseInfo->u.acceptedResponse.pThingName != NULL )
        {
            IotLogInfo( "ThingName = %.*s",
                        pResponseInfo->u.acceptedResponse.thingNameLength,
                        pResponseInfo->u.acceptedResponse.pThingName );
        }

        if( pResponseInfo->u.acceptedResponse.numOfConfigurationEntries > 0 )
        {
            for( size_t configIndex = 0;
                 configIndex < pResponseInfo->u.acceptedResponse.numOfConfigurationEntries;
                 configIndex++ )
            {
                IotLogInfo( "Device Configuration" );

                IotLogInfo( "ConfigName = %.*s, ConfigData = %.*s ",
                            pResponseInfo->u.acceptedResponse.pDeviceConfigList[ configIndex ].keyLength,
                            pResponseInfo->u.acceptedResponse.pDeviceConfigList[ configIndex ].pKey,
                            pResponseInfo->u.acceptedResponse.pDeviceConfigList[ configIndex ].valueLength,
                            pResponseInfo->u.acceptedResponse.pDeviceConfigList[ configIndex ].pValue );
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
 * @brief Test group for Provisioning system tests.
 */
TEST_GROUP( Provisioning_System );

/*-----------------------------------------------------------*/

/**
 * @brief Test setup for Provisioning system tests.
 */
TEST_SETUP( Provisioning_System )
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

    /* Initialize the Provisioning library. */
    if( AwsIotProvisioning_Init( 0 ) != AWS_IOT_PROVISIONING_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to initialize Provisioning library." );
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

    /* Set the members of the connect info. Use the Provisioning Thing Name as the MQTT
     * client identifier. */
    connectInfo.awsIotMqttMode = true;
    connectInfo.pClientIdentifier = _pTestMqttClientId;
    connectInfo.clientIdentifierLength = strlen( _pTestMqttClientId );
    connectInfo.keepAliveSeconds = AWS_IOT_TEST_PROVISIONING_TIMEOUT;

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
                              AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                              &_mqttConnection );

    if( status != IOT_MQTT_SUCCESS )
    {
        TEST_FAIL_MESSAGE( "Failed to establish MQTT connection for Provisioning tests" );
    }

    /* Update the time of the last MQTT connect. */
    lastConnectTime = IotClock_GetTimeMs();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test tear down for Provisioning system tests.
 */
TEST_TEAR_DOWN( Provisioning_System )
{
    /* Disconnect the MQTT connection if it was created. */
    if( _mqttConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotMqtt_Disconnect( _mqttConnection, 0 );
        _mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    }

    AwsIotProvisioning_Cleanup();

    /* Clean up the MQTT library. */
    IotMqtt_Cleanup();

    /* Clean up the network stack. */
    IotTestNetwork_Cleanup();

    /* Clean up SDK. */
    IotSdk_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Test group runner for Provisioning system tests.
 */
TEST_GROUP_RUNNER( Provisioning_System )
{
    RUN_TEST_CASE( Provisioning_System, CreateKeysAndCertificateNominalCase );
    RUN_TEST_CASE( Provisioning_System, CreateCertFromCsrNominalCase );
    RUN_TEST_CASE( Provisioning_System, CreateCertFromCsrWithInvalidCsr );
    RUN_TEST_CASE( Provisioning_System, RegisterThingWithKeysAndCertNominalCase );
    RUN_TEST_CASE( Provisioning_System, RegisterThingWithCertFromCsrNominalCase );
}

/*-----------------------------------------------------------*/

/**
 * @brief Verifies the behavior of the CreateKeysAndCertificate API in making
 * a request with AWS IoT Core for creation of key-pair and certificate.
 */
TEST( Provisioning_System, CreateKeysAndCertificateNominalCase )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _printKeysAndCertificateCallback
    };

    status = AwsIotProvisioning_CreateKeysAndCertificate( _mqttConnection,
                                                          0,
                                                          AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                                          &callbackInfo );

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, status );
}

/**
 * @brief Verifies the behavior of the CreateCertificateFromCsr API in making
 * a request for certificate-creation from CSR with the server.
 */
TEST( Provisioning_System, CreateCertFromCsrNominalCase )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateCertFromCsrCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _printCertificateFromCsrCallback
    };

    status = AwsIotProvisioning_CreateCertificateFromCsr( _mqttConnection,
                                                          IOT_MQTT_QOS_1,
                                                          AWS_IOT_TEST_PROVISIONING_CSR_PEM,
                                                          strlen( AWS_IOT_TEST_PROVISIONING_CSR_PEM ),
                                                          AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                                          &callbackInfo );

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, status );
}

/**
 * @brief Verifies that the CreateCertificateFromCsr API returns an error and correctly
 * parses a rejected server response server when called with an invalid CSR string.
 */
TEST( Provisioning_System, CreateCertFromCsrWithInvalidCsr )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;
    AwsIotProvisioningCreateCertFromCsrCallbackInfo_t callbackInfo =
    {
        .userParam = NULL,
        .function  = _checkInvalidCsrServerResponseCallback
    };

    const char * pInvalidCsr = "GibberishCsr";

    status = AwsIotProvisioning_CreateCertificateFromCsr( _mqttConnection,
                                                          IOT_MQTT_QOS_1,
                                                          pInvalidCsr,
                                                          strlen( pInvalidCsr ),
                                                          AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                                          &callbackInfo );

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SERVER_REFUSED, status );
}

/**
 * @brief Tests the behavior of the RegisterThing API function in the workflow when
 * keys are generated through the CreateKeysAndCertificate API.
 */
TEST( Provisioning_System, RegisterThingWithKeysAndCertNominalCase )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    AwsIotProvisioningRegisterThingCallbackInfo_t registerThingCallback =
    {
        .userParam = NULL,
        .function  = _printRegisterThingResponseCallback
    };

    /* To test the Provisioning RegisterThing API, we need to request credentials from the Provisioning
     * CreateKeysAndCertificate API,
     * that */
    /* we will use for provisioning in the test. */

    _certIdAndOwnershipTokenContext_t newCertificateContext;

    newCertificateContext.pCertificateIdBuffer = NULL;
    newCertificateContext.certificateIdLength = 0;
    newCertificateContext.pCertificateOwnershipToken = NULL;
    newCertificateContext.tokenLength = 0;

    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t createNewCredsCallback =
    {
        .userParam = &newCertificateContext,
        .function  = _storeDataFromKeysAndCertResponseCallback
    };

    /* Obtain new certificate and ownership token for testing provisioning API. */
    status = AwsIotProvisioning_CreateKeysAndCertificate( _mqttConnection,
                                                          0,
                                                          AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                                          &createNewCredsCallback );

    AwsIotProvisioningRegisterThingRequestInfo_t requestInfo;

    requestInfo.pDeviceCertificateId = newCertificateContext.pCertificateIdBuffer;
    requestInfo.deviceCertificateIdLength = newCertificateContext.certificateIdLength;
    requestInfo.pCertificateOwnershipToken = newCertificateContext.pCertificateOwnershipToken;
    requestInfo.ownershipTokenLength = newCertificateContext.tokenLength;
    requestInfo.pTemplateName = AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME;
    requestInfo.templateNameLength = ( sizeof( AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME ) - 1 );
    requestInfo.pParametersStart = _pTestParameters;
    requestInfo.numOfParameters = sizeof( _pTestParameters ) /
                                  sizeof( AwsIotProvisioningRequestParameterEntry_t );

    /* Call the API under test. */
    status = AwsIotProvisioning_RegisterThing( _mqttConnection,
                                               &requestInfo,
                                               AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                               &registerThingCallback );


    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, status );

    /* Test Cleanup */

    /* Release the certificate data buffers. */
    if( newCertificateContext.pCertificateIdBuffer != NULL )
    {
        IotTest_Free( newCertificateContext.pCertificateIdBuffer );
    }

    if( newCertificateContext.pCertificateOwnershipToken != NULL )
    {
        IotTest_Free( newCertificateContext.pCertificateOwnershipToken );
    }
}

/**
 * @brief Tests the behavior of the RegisterThing API function in the workflow when
 * keys are generated by generated through the CreateCertificateFromCsr API
 */
TEST( Provisioning_System, RegisterThingWithCertFromCsrNominalCase )
{
    AwsIotProvisioningError_t status = AWS_IOT_PROVISIONING_SUCCESS;

    AwsIotProvisioningRegisterThingCallbackInfo_t registerThingCallback =
    {
        .userParam = NULL,
        .function  = _printRegisterThingResponseCallback
    };

    /* To test the Provisioning RegisterThing API, we need to request credentials from the Provisioning
     * CreateCertificateFromCsr API, that */
    /* we will use for provisioning in the test. */

    _certIdAndOwnershipTokenContext_t newCertificateContext;

    newCertificateContext.pCertificateIdBuffer = NULL;
    newCertificateContext.certificateIdLength = 0;
    newCertificateContext.pCertificateOwnershipToken = NULL;
    newCertificateContext.tokenLength = 0;

    AwsIotProvisioningCreateCertFromCsrCallbackInfo_t certFromCsrCallback =
    {
        .userParam = &newCertificateContext,
        .function  = _storeDataOfCerFromCsrResponseCallback
    };

    /* Obtain new certificate and ownership token for testing provisioning API. */
    status = AwsIotProvisioning_CreateCertificateFromCsr( _mqttConnection,
                                                          IOT_MQTT_QOS_1,
                                                          AWS_IOT_TEST_PROVISIONING_CSR_PEM,
                                                          strlen( AWS_IOT_TEST_PROVISIONING_CSR_PEM ),
                                                          AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                                          &certFromCsrCallback );

    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, status );


    AwsIotProvisioningRegisterThingRequestInfo_t requestInfo;

    requestInfo.pDeviceCertificateId = newCertificateContext.pCertificateIdBuffer;
    requestInfo.deviceCertificateIdLength = newCertificateContext.certificateIdLength;
    requestInfo.pCertificateOwnershipToken = newCertificateContext.pCertificateOwnershipToken;
    requestInfo.ownershipTokenLength = newCertificateContext.tokenLength;
    requestInfo.pTemplateName = AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME;
    requestInfo.templateNameLength = ( sizeof( AWS_IOT_TEST_PROVISIONING_TEMPLATE_NAME ) - 1 );
    requestInfo.pParametersStart = _pTestParameters;
    requestInfo.numOfParameters = sizeof( _pTestParameters ) /
                                  sizeof( AwsIotProvisioningRequestParameterEntry_t );

    /* Call the API under test. */
    status = AwsIotProvisioning_RegisterThing( _mqttConnection,
                                               &requestInfo,
                                               AWS_IOT_TEST_PROVISIONING_TIMEOUT,
                                               &registerThingCallback );


    TEST_ASSERT_EQUAL( AWS_IOT_PROVISIONING_SUCCESS, status );

    /* Test Cleanup */

    /* Release the certificate data buffers. */
    if( newCertificateContext.pCertificateIdBuffer != NULL )
    {
        IotTest_Free( newCertificateContext.pCertificateIdBuffer );
    }

    if( newCertificateContext.pCertificateOwnershipToken != NULL )
    {
        IotTest_Free( newCertificateContext.pCertificateOwnershipToken );
    }
}
