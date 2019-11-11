/*
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_demo_onboarding.c
 * @brief Demonstrates usage of the Thing Onboarding library.
 *
 * This program demonstrates the using Onboarding documents to toggle a state called
 * "powerOn" in a remote device.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Set up logging for this demo. */
#include "iot_demo_logging.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Onboarding include. */
#include "aws_iot_onboarding.h"

/* JSON utilities include. */
#include "iot_json_utils.h"

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration settings.
 */
#ifndef AWS_IOT_DEMO_ONBOARDING_UPDATE_COUNT
    #define AWS_IOT_DEMO_ONBOARDING_UPDATE_COUNT         ( 20 )
#endif
#ifndef AWS_IOT_DEMO_ONBOARDING_TIMEOUT_PERIOD_MS
    #define AWS_IOT_DEMO_ONBOARDING_TIMEOUT_PERIOD_MS    ( 50000 )
#endif
/** @endcond */

/**
 * @brief The keep-alive interval used for this demo.
 *
 * An MQTT ping request will be sent periodically at this interval.
 */
#define KEEP_ALIVE_SECONDS              ( 60 )

/**
 * @brief The timeout for Onboarding and MQTT operations in this demo.
 */
#define TIMEOUT_MS                      ( 5000 )

/**
 * @brief The name for the provisioning template that will be used for provisioning the demo app.
 */
#define PROVISIONING_TEMPLATE_NAME      "CI_TEST_TEMPLATE"

/**
 * @brief The parameter that will be used for provisioning the demo application.
 */
#define PROVISIONING_PARAMETER_NAME     "DeviceLocation"
#define PROVISIONING_PARAMETER_VALUE    "Seattle"
#define NUM_OF_PROVISIONING_PARAMS      1u

/**
 * @brief Type for the callback context for the #AwsIotOnboarding_GetDeviceCredentials API.
 * It will be used for storing the received Certificate ID string that will be provided in the callback.
 */
typedef struct _demoProvisionDeviceCallbackContext
{
    char * pCertificateIdBuffer;
    size_t certificateIdLength;
} _demoProvisionDeviceCallbackContext_t;

/*-----------------------------------------------------------*/

/* Declaration of demo function. */
int RunOnboardingDemo( bool awsIotMqttMode,
                       const char * pIdentifier,
                       void * pNetworkServerInfo,
                       void * pNetworkCredentialInfo,
                       const IotNetworkInterface_t * pNetworkInterface );

/*-----------------------------------------------------------*/

/**
 * @brief Prints the rejected reponse information received from the server.
 */
static void _printRejectedResponse( const AwsIotOnboardingRejectedResponse_t * pResponseInfo )
{
    IotLogError( "ErrorCode={%.*s}\n ErrorMessage={%.*s}\n",
                 pResponseInfo->errorCodeLength, pResponseInfo->pErrorCode,
                 pResponseInfo->errorMessageLength, pResponseInfo->pErrorMessage );
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for displaying the credentials sent by the server (if server is successful), and
 * copying the Certificate ID data obtained from the server issued with the new device credentials.
 *
 * @param[in] contextParam The context of the callback containing buffers to copy the credentials to.
 * @param[in] pResponseInfo The device credentials information obtained from the server that will be copied into the
 * shared buffers of the demo.
 */
static void _demoDeviceCredentialsCallback( void * contextParam,
                                            const AwsIotOnboardingGetDeviceCredentialsResponse_t * pResponseInfo )
{
    _demoProvisionDeviceCallbackContext_t * certificateIdContext = ( _demoProvisionDeviceCallbackContext_t * ) contextParam;

    IotLogInfo( "Received StatusCode={%d}", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_ONBOARDING_SERVER_STATUS_ACCEPTED )
    {
        /* Allocate buffer space for storing the certificate ID obtained from the server. */
        certificateIdContext->pCertificateIdBuffer = malloc( pResponseInfo->u.acceptedResponse.certificateIdLength + 1 );

        /* Copy the size of the Certificate ID string. */
        certificateIdContext->certificateIdLength = pResponseInfo->u.acceptedResponse.certificateIdLength;

        /* Copy the certificate ID into the buffer. */
        if( certificateIdContext->pCertificateIdBuffer != NULL )
        {
            memcpy( certificateIdContext->pCertificateIdBuffer,
                    pResponseInfo->u.acceptedResponse.pCertificateId,
                    pResponseInfo->u.acceptedResponse.certificateIdLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( certificateIdContext->pCertificateIdBuffer + pResponseInfo->u.acceptedResponse.certificateIdLength ) = '\0';
        }

        /* Print the certificate Pem and private key data received. This is ONLY for the demo purpose, STORE THE
         * PRIVATE KEY SECURELY! */
        IotLogInfo( "\n Certificate PEM = %.*s \n Certificate ID = %.*s \n DREADED PRIVATE KEY = %.*s \n",
                    pResponseInfo->u.acceptedResponse.deviceCertificateLength,
                    pResponseInfo->u.acceptedResponse.pDeviceCertificate,
                    pResponseInfo->u.acceptedResponse.certificateIdLength,
                    pResponseInfo->u.acceptedResponse.pCertificateId,
                    pResponseInfo->u.acceptedResponse.privateKeyLength,
                    pResponseInfo->u.acceptedResponse.pPrivateKey );
    }
    else
    {
        IotLogInfo( "Oops, server rejected request for creating new credentials. Consider re-running the demo!" );
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for displaying onboarding information sent by the server, if the onboarding request is successful.
 *
 * @param[in] contextParam Unused parameter for the demo.
 * @param[in] pResponseInfo The information in the response received from the server.
 */
static void _demoOnboardDeviceCallback( void * contextParam,
                                        const AwsIotOnboardingOnboardDeviceResponse_t * pResponseInfo )
{
    ( void ) contextParam;

    IotLogInfo( "Received StatusCode={%d}", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_ONBOARDING_SERVER_STATUS_ACCEPTED )
    {
        if( pResponseInfo->u.acceptedResponse.pThingName != NULL )
        {
            IotLogInfo( "ThingName = %.*s",
                        pResponseInfo->u.acceptedResponse.thingNameLength,
                        pResponseInfo->u.acceptedResponse.pThingName );
        }

        if( pResponseInfo->u.acceptedResponse.numOfConfigurationEntries > 0 )
        {
            const AwsIotOnboardingResponseDeviceConfigurationEntry_t * pConfigurationList =
                pResponseInfo->u.acceptedResponse.pDeviceConfigList;

            for( size_t configIndex = 0;
                 configIndex < pResponseInfo->u.acceptedResponse.numOfConfigurationEntries; configIndex++ )
            {
                IotLogInfo( "Device Configuration no. %d\nConfigName = %.*s, ConfigData = %.*s ",
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
        IotLogInfo( "Oops, server rejected request for onboarding the demo app.Consider re - running the demo !" );
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Initialize the the MQTT library and the Onboarding library.
 *
 * @return `EXIT_SUCCESS` if all libraries were successfully initialized;
 * `EXIT_FAILURE` otherwise.
 */
static int _initializeDemo( void )
{
    int status = EXIT_SUCCESS;
    IotMqttError_t mqttInitStatus = IOT_MQTT_SUCCESS;
    AwsIotOnboardingError_t onboardingInitStatus = AWS_IOT_ONBOARDING_SUCCESS;

    /* Flags to track cleanup on error. */
    bool mqttInitialized = false;

    /* Initialize the MQTT library. */
    mqttInitStatus = IotMqtt_Init();

    if( mqttInitStatus == IOT_MQTT_SUCCESS )
    {
        mqttInitialized = true;
    }
    else
    {
        status = EXIT_FAILURE;
    }

    /* Initialize the Onboarding library. */
    if( status == EXIT_SUCCESS )
    {
        /* Use the default MQTT timeout. */
        onboardingInitStatus = AwsIotOnboarding_Init( 0 );

        if( onboardingInitStatus != AWS_IOT_ONBOARDING_SUCCESS )
        {
            status = EXIT_FAILURE;
        }
    }

    /* Clean up on error. */
    if( status == EXIT_FAILURE )
    {
        if( mqttInitialized == true )
        {
            IotMqtt_Cleanup();
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Clean up the the MQTT library and the Onboarding library.
 */
static void _cleanupDemo( void )
{
    AwsIotOnboarding_Cleanup();
    IotMqtt_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Establish a new connection to the MQTT server for the Onboarding demo.
 *
 * @param[in] pIdentifier NULL-terminated MQTT client identifier. The Onboarding
 * demo will use the Thing Name as the client identifier.
 * @param[in] pNetworkServerInfo Passed to the MQTT connect function when
 * establishing the MQTT connection.
 * @param[in] pNetworkCredentialInfo Passed to the MQTT connect function when
 * establishing the MQTT connection.
 * @param[in] pNetworkInterface The network interface to use for this demo.
 * @param[out] pMqttConnection Set to the handle to the new MQTT connection.
 *
 * @return `EXIT_SUCCESS` if the connection is successfully established; `EXIT_FAILURE`
 * otherwise.
 */
static int _establishMqttConnection( const char * pIdentifier,
                                     void * pNetworkServerInfo,
                                     void * pNetworkCredentialInfo,
                                     const IotNetworkInterface_t * pNetworkInterface,
                                     IotMqttConnection_t * pMqttConnection )
{
    int status = EXIT_SUCCESS;
    IotMqttError_t connectStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttNetworkInfo_t networkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
    IotMqttConnectInfo_t connectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    /* Set the members of the network info not set by the initializer. This
     * struct provided information on the transport layer to the MQTT connection. */
    networkInfo.createNetworkConnection = true;
    networkInfo.u.setup.pNetworkServerInfo = pNetworkServerInfo;
    networkInfo.u.setup.pNetworkCredentialInfo = pNetworkCredentialInfo;
    networkInfo.pNetworkInterface = pNetworkInterface;

    /* Set the members of the connection info not set by the initializer. */
    connectInfo.awsIotMqttMode = true;
    connectInfo.cleanSession = true;
    connectInfo.keepAliveSeconds = KEEP_ALIVE_SECONDS;

    /* AWS IoT recommends the use of the Thing Name as the MQTT client ID. */
    connectInfo.pClientIdentifier = pIdentifier;
    connectInfo.clientIdentifierLength = ( uint16_t ) strlen( pIdentifier );

    /* Establish the MQTT connection. */
    connectStatus = IotMqtt_Connect( &networkInfo,
                                     &connectInfo,
                                     TIMEOUT_MS,
                                     pMqttConnection );

    if( connectStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "MQTT CONNECT returned error %s.",
                     IotMqtt_strerror( connectStatus ) );

        status = EXIT_FAILURE;
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief The function that runs the Onboarding demo, called by the demo runner.
 *
 * @param[in] awsIotMqttMode Ignored for the Onboarding demo.
 * @param[in] pIdentifier NULL-terminated Onboarding Thing Name.
 * @param[in] pNetworkServerInfo Passed to the MQTT connect function when
 * establishing the MQTT connection for Onboardings.
 * @param[in] pNetworkCredentialInfo Passed to the MQTT connect function when
 * establishing the MQTT connection for Onboardings.
 * @param[in] pNetworkInterface The network interface to use for this demo.
 *
 * @return `EXIT_SUCCESS` if the demo completes successfully; `EXIT_FAILURE` otherwise.
 */
int RunOnboardingDemo( bool awsIotMqttMode,
                       const char * pIdentifier,
                       void * pNetworkServerInfo,
                       void * pNetworkCredentialInfo,
                       const IotNetworkInterface_t * pNetworkInterface )
{
    /* Return value of this function and the exit status of this program. */
    int status = 0;

    /* Handle of the MQTT connection used in this demo. */
    IotMqttConnection_t mqttConnection = IOT_MQTT_CONNECTION_INITIALIZER;

    /* Callbacks for the library APIs. */
    AwsIotOnboardingGetDeviceCredentialsCallbackInfo_t deviceCredentialsCallback = AWS_IOT_ONBOARDING_GET_DEVICE_CREDENTIALS_CALLBACK_INFO_INITIALIZER;
    AwsIotOnboardingOnboardDeviceCallbackInfo_t onboardDeviceResponseCallback = AWS_IOT_ONBOARDING_ONBOARD_DEVICE_CALLBACK_INFO_INITIALIZER;

    /* Represents memory that will be allocated to store the Certificate ID that will be provided by the credential
     * requesting API through the callback. */
    _demoProvisionDeviceCallbackContext_t newCertificateIdDataContext;

    /* Request data for onboarding the demo application. */
    AwsIotOnboardingOnboardDeviceRequestInfo_t requestInfo;

    /* Flags for tracking which cleanup functions must be called. */
    bool librariesInitialized = false, connectionEstablished = false;

    /* The first parameter of this demo function is not used. Onboardings are specific
     * to AWS IoT, so this value is hardcoded to true whenever needed. */
    ( void ) awsIotMqttMode;

    /* This will be used for tracking the return code from the Provisioning APIs. */
    AwsIotOnboardingError_t requestStatus = AWS_IOT_ONBOARDING_SUCCESS;

    AwsIotOnboardingRequestParameterEntry_t provisioningParameters;
    provisioningParameters.pParameterKey = PROVISIONING_PARAMETER_NAME;
    provisioningParameters.parameterKeyLength = ( size_t ) ( sizeof( PROVISIONING_PARAMETER_NAME ) - 1 );
    provisioningParameters.pParameterValue = PROVISIONING_PARAMETER_VALUE;
    provisioningParameters.parameterValueLength = ( size_t ) ( sizeof( PROVISIONING_PARAMETER_VALUE ) - 1 );

    /* Determine the length of the client ID Name. */
    if( pIdentifier != NULL )
    {
        if( strlen( pIdentifier ) == 0 )
        {
            IotLogError( "The length of the MQTT client identifier must be nonzero." );

            status = EXIT_FAILURE;
        }
    }
    else
    {
        IotLogError( "A client identifier must be provided for the Onboarding demo." );

        status = EXIT_FAILURE;
    }

    /* Initialize the libraries required for this demo. */
    if( status == EXIT_SUCCESS )
    {
        status = _initializeDemo();
    }

    if( status == EXIT_SUCCESS )
    {
        /* Mark the libraries as initialized. */
        librariesInitialized = true;

        /* Establish a new MQTT connection. */
        status = _establishMqttConnection( pIdentifier,
                                           pNetworkServerInfo,
                                           pNetworkCredentialInfo,
                                           pNetworkInterface,
                                           &mqttConnection );
    }

    if( status == EXIT_SUCCESS )
    {
        /* Mark the MQTT connection as established. */
        connectionEstablished = true;

        /* Set the certificate ID pointer as context parameter to the credentials response processing callback. */
        deviceCredentialsCallback.userParam = &newCertificateIdDataContext;

        /* Set the callback function for handling device credentials that the server will send. */
        deviceCredentialsCallback.function = _demoDeviceCredentialsCallback;

        /* Call the API to get new device credentials for this demo, and check that the certificat ID data is populated.
         * */
        requestStatus = AwsIotOnboarding_GetDeviceCredentials( mqttConnection,
                                                               0,
                                                               AWS_IOT_DEMO_ONBOARDING_TIMEOUT_PERIOD_MS,
                                                               &deviceCredentialsCallback );

        if( requestStatus != AWS_IOT_ONBOARDING_SUCCESS )
        {
            status = EXIT_FAILURE;
            IotLogError( "Request to get new credentials failed, error %s ",
                         AwsIotOnboarding_strerror( requestStatus ) );
        }
        else if( newCertificateIdDataContext.pCertificateIdBuffer == NULL )
        {
            IotLogInfo( "Don 't have the Certificate ID to proceed for onboarding. So exiting...!" );
        }
        else
        {
            IotLogInfo( "Succeeded in receiving new device credentials!" );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Set the parameters for requesting onboarding. */
        requestInfo.pDeviceCertificateId = newCertificateIdDataContext.pCertificateIdBuffer;
        requestInfo.deviceCertificateIdLength = newCertificateIdDataContext.certificateIdLength;
        requestInfo.pTemplateIdentifier = PROVISIONING_TEMPLATE_NAME;
        requestInfo.templateIdentifierLength = sizeof( PROVISIONING_TEMPLATE_NAME ) - 1;
        requestInfo.pParametersStart = &provisioningParameters;
        requestInfo.numOfParameters = NUM_OF_PROVISIONING_PARAMS;

        /* Set the callback function for handling device credentials that the server will send. */
        onboardDeviceResponseCallback.function = _demoOnboardDeviceCallback;

        /* Call the API to onboard the demo application with the certificate ID that we received, and the template name
         * associated with the demo endpoint account. */
        requestStatus = AwsIotOnboarding_OnboardDevice( mqttConnection,
                                                        &requestInfo,
                                                        AWS_IOT_DEMO_ONBOARDING_TIMEOUT_PERIOD_MS,
                                                        &onboardDeviceResponseCallback );

        if( requestStatus != AWS_IOT_ONBOARDING_SUCCESS )
        {
            status = EXIT_FAILURE;
            IotLogError( "Failed to onboard demo application, error %s",
                         AwsIotOnboarding_strerror( requestStatus ) );
        }
        else
        {
            IotLogInfo( "Succeeded in onboarding our demo application!" );
        }
    }

    /* Disconnect the MQTT connection if it was established. */
    if( connectionEstablished == true )
    {
        IotMqtt_Disconnect( mqttConnection, 0 );
    }

    /* Clean up libraries if they were initialized. */
    if( librariesInitialized == true )
    {
        _cleanupDemo();
    }

    /* Release the Certificate ID buffer, if memory was allocated for it. */
    if( newCertificateIdDataContext.pCertificateIdBuffer != NULL )
    {
        free( newCertificateIdDataContext.pCertificateIdBuffer );
    }

    return status;
}

/*-----------------------------------------------------------*/
