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
 * @file aws_iot_demo_provisioning.c
 * @brief Demonstrates usage of the Thing Provisioning library.
 *
 * This program demonstrates the using Provisioning documents to toggle a state called
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

/* Provisioning include. */
#include "aws_iot_provisioning.h"

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration settings.
 */
#ifndef AWS_IOT_DEMO_PROVISIONING_UPDATE_COUNT
    #define AWS_IOT_DEMO_PROVISIONING_UPDATE_COUNT         ( 20 )
#endif
#ifndef AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS
    #define AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS    ( 5000 )
#endif
/** @endcond */

/**
 * @brief The keep-alive interval used for this demo.
 *
 * An MQTT ping request will be sent periodically at this interval.
 */
#define KEEP_ALIVE_SECONDS                         ( 60 )

/**
 * @brief The timeout for Provisioning and MQTT operations in this demo.
 */
#define TIMEOUT_MS                                 ( 5000 )

/**
 * @brief The parameter that will be used for provisioning the demo application.
 */
#define PROVISIONING_PARAMETER_LOCATION_NAME       "DeviceLocation"
#define PROVISIONING_PARAMETER_LOCATION_VALUE      "Seattle"
#define PROVISIONING_PARAMETER_SERIAL_NUM_NAME     "SerialNumber"
#define PROVISIONING_PARAMETER_SERIAL_NUM_VALUE    "1122334455667788"
#define NUM_OF_PROVISIONING_PARAMS                 2u

/**
 * @brief The template name to use for provisioning the demo application.
 */
static const char pTemplateName[] = AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME;

/**
 * @brief Type for the context parameter for the #AwsIotProvisioning_KeysAndCertificateCallbackInfo_t callback.
 * It will be used for storing the received Certificate ID and the ownership token data received from the server through
 * the callback, so that can be used for provisioning the demo application.
 */
typedef struct _demoKeysAndCertificateCallbackContext
{
    char * pCertificateIdBuffer;
    size_t certificateIdLength;
    char * pCertificateOwnershipToken;
    size_t tokenLength;
} _demoKeysAndCertificateCallbackContext_t;

/*-----------------------------------------------------------*/

/* Declaration of demo function. */
int RunProvisioningDemo( bool awsIotMqttMode,
                         const char * pIdentifier,
                         void * pNetworkServerInfo,
                         void * pNetworkCredentialInfo,
                         const IotNetworkInterface_t * pNetworkInterface );

/*-----------------------------------------------------------*/

/**
 * @brief Prints the rejected reponse information received from the server.
 */
static void _printRejectedResponse( const AwsIotProvisioningRejectedResponse_t * pResponseInfo )
{
    IotLogError( "ErrorCode={%.*s}\n ErrorMessage={%.*s}\n",
                 pResponseInfo->errorCodeLength, pResponseInfo->pErrorCode,
                 pResponseInfo->errorMessageLength, pResponseInfo->pErrorMessage );
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for displaying the credentials sent by the server (if server is successful), and
 * copying the Certificate ID and ownership token data obtained from the server issued with the new device credentials.
 *
 * @param[in] contextParam The context of the callback containing buffers to copy the credentials to.
 * @param[in] pResponseInfo The device credentials information obtained from the server that will be copied into the
 * shared buffers of the demo.
 */
static void _demoKeysAndCertificateCallback( void * contextParam,
                                             const AwsIotProvisioningCreateKeysAndCertificateResponse_t * pResponseInfo )
{
    _demoKeysAndCertificateCallbackContext_t * certificateIdTokenContext =
        ( _demoKeysAndCertificateCallbackContext_t * ) contextParam;

    IotLogInfo( "Received StatusCode={%d}", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        /* Allocate buffer space for storing the certificate ID obtained from the server. */
        certificateIdTokenContext->pCertificateIdBuffer =
            Iot_DefaultMalloc( pResponseInfo->u.acceptedResponse.certificateIdLength + 1 );

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
            Iot_DefaultMalloc( pResponseInfo->u.acceptedResponse.ownershipTokenLength + 1 );

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

        /* Print the received credentials information. This is ONLY for the demonstration purpose, STORE THE
         * PRIVATE KEY SECURELY! */
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
        IotLogInfo( "Oops, server rejected request for creating new credentials. Consider re-running the demo!" );
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for displaying provisioning information sent by the server, if the provisioning request is
 * successful.
 *
 * @param[in] contextParam Unused parameter for the demo.
 * @param[in] pResponseInfo The information in the response received from the server.
 */
static void _demoRegisterThingCallback( void * contextParam,
                                        const AwsIotProvisioningRegisterThingResponse_t * pResponseInfo )
{
    ( void ) contextParam;

    IotLogInfo( "Received StatusCode={%d}", pResponseInfo->statusCode );

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
            const AwsIotProvisioningResponseDeviceConfigurationEntry_t * pConfigurationList =
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
        IotLogInfo( "Oops, server rejected request for provisioning the demo app.Consider re - running the demo !" );
        _printRejectedResponse( &pResponseInfo->u.rejectedResponse );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Initialize the the MQTT library and the Provisioning library.
 *
 * @return `EXIT_SUCCESS` if all libraries were successfully initialized;
 * `EXIT_FAILURE` otherwise.
 */
static int _initializeDemo( void )
{
    int status = EXIT_SUCCESS;
    IotMqttError_t mqttInitStatus = IOT_MQTT_SUCCESS;
    AwsIotProvisioningError_t provisioningInitStatus = AWS_IOT_PROVISIONING_SUCCESS;

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

    /* Initialize the Provisioning library. */
    if( status == EXIT_SUCCESS )
    {
        /* Use the default MQTT timeout. */
        provisioningInitStatus = AwsIotProvisioning_Init( 0 );

        if( provisioningInitStatus != AWS_IOT_PROVISIONING_SUCCESS )
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
 * @brief Clean up the the MQTT library and the Provisioning library.
 */
static void _cleanupDemo( void )
{
    AwsIotProvisioning_Cleanup();
    IotMqtt_Cleanup();
}

/*-----------------------------------------------------------*/

/**
 * @brief Establish a new connection to the MQTT server for the Provisioning demo.
 *
 * @param[in] pIdentifier NULL-terminated MQTT client identifier. The Provisioning
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
 * @brief The function that runs the Provisioning demo, called by the demo runner.
 *
 * @param[in] awsIotMqttMode Ignored for the Provisioning demo.
 * @param[in] pIdentifier NULL-terminated Provisioning Thing Name.
 * @param[in] pNetworkServerInfo Passed to the MQTT connect function when
 * establishing the MQTT connection for testing the Fleet Provisioning feature of AWS Iot Core service.
 * @param[in] pNetworkCredentialInfo Passed to the MQTT connect function when
 * establishing the MQTT connection for testing the Fleet Provisioning feature of AWS Iot Core service.
 * @param[in] pNetworkInterface The network interface to use for this demo.
 *
 * @return `EXIT_SUCCESS` if the demo completes successfully; `EXIT_FAILURE` otherwise.
 */
int RunProvisioningDemo( bool awsIotMqttMode,
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
    AwsIotProvisioningCreateKeysAndCertificateCallbackInfo_t keysAndCertificateCallback = AWS_IOT_PROVISIONING_CREATE_KEYS_AND_CERTIFICATE_CALLBACK_INFO_INITIALIZER;
    AwsIotProvisioningRegisterThingCallbackInfo_t registerThingResponseCallback = AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;

    /* Represents memory that will be allocated to store the Certificate ID that will be provided by the credential
     * requesting API through the callback. */
    _demoKeysAndCertificateCallbackContext_t newCertificateDataContext;

    newCertificateDataContext.pCertificateIdBuffer = NULL;
    newCertificateDataContext.certificateIdLength = 0;
    newCertificateDataContext.pCertificateOwnershipToken = NULL;
    newCertificateDataContext.tokenLength = 0;

    /* Request data for provisioning the demo application. */
    AwsIotProvisioningRegisterThingRequestInfo_t requestInfo;

    /* Flags for tracking which cleanup functions must be called. */
    bool librariesInitialized = false, connectionEstablished = false;

    /* The first parameter of this demo function is not used. Provisioning feature is specific
     * to AWS IoT, so this value is hardcoded to true whenever needed. */
    ( void ) awsIotMqttMode;

    /* This will be used for tracking the return code from the Provisioning APIs. */
    AwsIotProvisioningError_t requestStatus = AWS_IOT_PROVISIONING_SUCCESS;

    /* Set the parameters that will be used as "context" for provisioning the demo application. */
    AwsIotProvisioningRequestParameterEntry_t provisioningParameters[ 2 ];
    provisioningParameters[ 0 ].pParameterKey = PROVISIONING_PARAMETER_LOCATION_NAME;
    provisioningParameters[ 0 ].parameterKeyLength = ( size_t ) ( sizeof( PROVISIONING_PARAMETER_LOCATION_NAME ) - 1 );
    provisioningParameters[ 0 ].pParameterValue = PROVISIONING_PARAMETER_LOCATION_VALUE;
    provisioningParameters[ 0 ].parameterValueLength = ( size_t ) ( sizeof( PROVISIONING_PARAMETER_LOCATION_VALUE ) - 1 );
    provisioningParameters[ 1 ].pParameterKey = PROVISIONING_PARAMETER_SERIAL_NUM_NAME;
    provisioningParameters[ 1 ].parameterKeyLength = ( size_t ) ( sizeof( PROVISIONING_PARAMETER_SERIAL_NUM_NAME ) - 1 );
    provisioningParameters[ 1 ].pParameterValue = PROVISIONING_PARAMETER_SERIAL_NUM_VALUE;
    provisioningParameters[ 1 ].parameterValueLength = ( size_t ) ( sizeof( PROVISIONING_PARAMETER_SERIAL_NUM_VALUE ) - 1 );

    /* Determine if a provisioning template name has been specified. */
    if( strlen( pTemplateName ) == 0 )
    {
        IotLogError( "A valid provisioning template name must be provided." );
        status = EXIT_FAILURE;
    }

    /* Determine the length of the client ID Name. */
    if( ( status != EXIT_FAILURE ) && ( pIdentifier != NULL ) )
    {
        if( strlen( pIdentifier ) == 0 )
        {
            IotLogError( "The length of the MQTT client identifier must be nonzero." );

            status = EXIT_FAILURE;
        }
    }
    else if( pIdentifier == NULL )
    {
        IotLogError( "A client identifier must be provided for the Provisioning demo." );

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
        keysAndCertificateCallback.userParam = &newCertificateDataContext;

        /* Set the callback function for handling device credentials that the server will send. */
        keysAndCertificateCallback.function = _demoKeysAndCertificateCallback;

        /* Call the API to get new device credentials for this demo, and check that the certificat ID data is populated.
         * */
        requestStatus = AwsIotProvisioning_CreateKeysAndCertificate( mqttConnection,
                                                                     0,
                                                                     AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS,
                                                                     &keysAndCertificateCallback );

        if( requestStatus != AWS_IOT_PROVISIONING_SUCCESS )
        {
            status = EXIT_FAILURE;
            IotLogError( "Request to get new credentials failed, error %s ",
                         AwsIotProvisioning_strerror( requestStatus ) );
        }
        else if( ( newCertificateDataContext.pCertificateIdBuffer == NULL ) ||
                 ( newCertificateDataContext.pCertificateOwnershipToken == NULL ) )
        {
            IotLogInfo( "Don't have either the Certificate ID OR the Certificate Ownership Token (or both) to proceed with provisioning. So exiting...!" );
        }
        else
        {
            IotLogInfo( "Succeeded in receiving new device credentials!" );
        }
    }

    if( status == EXIT_SUCCESS )
    {
        /* Set the parameters for requesting provisioning. */
        requestInfo.pDeviceCertificateId = newCertificateDataContext.pCertificateIdBuffer;
        requestInfo.deviceCertificateIdLength = newCertificateDataContext.certificateIdLength;
        requestInfo.pCertificateOwnershipToken = newCertificateDataContext.pCertificateOwnershipToken;
        requestInfo.ownershipTokenLength = newCertificateDataContext.tokenLength;
        requestInfo.pTemplateName = AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME;
        requestInfo.templateNameLength = sizeof( AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME ) - 1;
        requestInfo.pParametersStart = &provisioningParameters[ 0 ];
        requestInfo.numOfParameters = NUM_OF_PROVISIONING_PARAMS;

        /* Set the callback function for handling device credentials that the server will send. */
        registerThingResponseCallback.function = _demoRegisterThingCallback;

        /* Call the API to provision the demo application with the certificate ID that we received, and the template
         * name
         * associated with the demo endpoint account. */
        requestStatus = AwsIotProvisioning_RegisterThing( mqttConnection,
                                                          &requestInfo,
                                                          AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS,
                                                          &registerThingResponseCallback );

        if( requestStatus != AWS_IOT_PROVISIONING_SUCCESS )
        {
            status = EXIT_FAILURE;
            IotLogError( "Failed to provision demo application, error %s",
                         AwsIotProvisioning_strerror( requestStatus ) );
        }
        else
        {
            IotLogInfo( "Succeeded in provisioning our demo application!" );
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
    if( newCertificateDataContext.pCertificateIdBuffer != NULL )
    {
        Iot_DefaultFree( newCertificateDataContext.pCertificateIdBuffer );
    }

    /* Release the ownership token buffer, if memory was allocated for it. */
    if( newCertificateDataContext.pCertificateOwnershipToken != NULL )
    {
        Iot_DefaultFree( newCertificateDataContext.pCertificateOwnershipToken );
    }

    return status;
}

/*-----------------------------------------------------------*/
