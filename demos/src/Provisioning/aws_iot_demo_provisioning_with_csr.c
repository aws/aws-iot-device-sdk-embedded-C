/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_demo_provisioning_with_csr.c
 * @brief Demonstrates usage of the Provisioning library for the use-case
 * involving creation of certificate with a Certificate-Signing Request
 * to AWS IoT.
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
#ifndef AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS
    #define AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS    ( 5000 )
#endif

#ifndef AWS_IOT_DEMO_PROVISIONING_CSR_PEM
    #error "The AWS_IOT_DEMO_PROVISIONING_CSR_PEM should be defined for the demo."
#endif
/** @endcond */

/**
 * @brief The keep-alive interval used for this demo.
 *
 * An MQTT ping request will be sent periodically at this interval.
 */
#define KEEP_ALIVE_SECONDS    ( 60 )

/**
 * @brief The timeout for Provisioning and MQTT operations in this demo.
 */
#define TIMEOUT_MS            ( 5000 )

/**
 * @brief The template name to use for provisioning the demo application.
 */
static const char pTemplateName[] = AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME;

/**
 * @brief Stores the received certificate ID and certificate ownership token from the server.
 */
typedef struct _demoCertFromCsrCallbackContext
{
    char * pCertificateIdBuffer;  /**< @brief Buffer containing the certificate ID returned by the server. */
    size_t certificateIdLength;   /**< @brief Length of the certificate ID* buffer. */
    char * pOwnershipTokenBuffer; /**< @brief Buffer containing the certificate ownership token returned
                                   * by the server. */
    size_t tokenLength;           /**< @brief Length of the ownership token. */
} _demoCertFromCsrCallbackContext_t;

/*-----------------------------------------------------------*/

/* Declaration of demo function. */
int RunProvisioningWithCsrDemo( bool awsIotMqttMode,
                                const char * pIdentifier,
                                void * pNetworkServerInfo,
                                void * pNetworkCredentialInfo,
                                const IotNetworkInterface_t * pNetworkInterface );

/*-----------------------------------------------------------*/

/**
 * @brief Prints the rejected response information received from the server.
 */
static void _printRejectedResponse( const AwsIotProvisioningRejectedResponse_t * pResponseInfo )
{
    IotLogError( "ErrorCode={%.*s}\n ErrorMessage={%.*s}\n",
                 pResponseInfo->errorCodeLength, pResponseInfo->pErrorCode,
                 pResponseInfo->errorMessageLength, pResponseInfo->pErrorMessage );
}

/*-----------------------------------------------------------*/

/**
 * @brief Callback for displaying the information in the server response. If the response is successful (i.e. contains
 * credentials), the Certificate ID and ownership token data will be copied into buffers for use later in the demo.
 *
 * @param[in] contextParam The context of the callback containing buffers to copy the credentials to.
 * @param[in] pResponseInfo The device credentials information obtained from the server that will be copied into the
 * shared buffers of the demo.
 */
static void _demoCertFromCsrCallback( void * contextParam,
                                      const AwsIotProvisioningCreateCertFromCsrResponse_t * pResponseInfo )
{
    _demoCertFromCsrCallbackContext_t * certIdTokenContext =
        ( _demoCertFromCsrCallbackContext_t * ) contextParam;

    IotLogInfo( "Server response callback invoked: Received server response: "
                "StatusCode={%d}", pResponseInfo->statusCode );

    if( pResponseInfo->statusCode == AWS_IOT_PROVISIONING_SERVER_STATUS_ACCEPTED )
    {
        /* Allocate buffer space for storing the certificate ID obtained from the server. */
        certIdTokenContext->pCertificateIdBuffer =
            Iot_DefaultMalloc( pResponseInfo->u.acceptedResponse.certIdLength + 1 );

        /* Copy the certificate ID into the buffer. */
        if( certIdTokenContext->pCertificateIdBuffer != NULL )
        {
            /* Copy the size of the Certificate ID string. */
            certIdTokenContext->certificateIdLength = pResponseInfo->u.acceptedResponse.certIdLength;

            memcpy( certIdTokenContext->pCertificateIdBuffer,
                    pResponseInfo->u.acceptedResponse.pCertId,
                    pResponseInfo->u.acceptedResponse.certIdLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( certIdTokenContext->pCertificateIdBuffer + pResponseInfo->u.acceptedResponse.certIdLength ) = '\0';
        }

        /* Allocate buffer space for storing the ownership token string obtained from the server. */
        certIdTokenContext->pOwnershipTokenBuffer =
            Iot_DefaultMalloc( pResponseInfo->u.acceptedResponse.ownershipTokenLength + 1 );

        /* Copy the ownership token into the buffer. */
        if( certIdTokenContext->pOwnershipTokenBuffer != NULL )
        {
            /* Copy the size of the ownership token string. */
            certIdTokenContext->tokenLength = pResponseInfo->u.acceptedResponse.ownershipTokenLength;

            memcpy( certIdTokenContext->pOwnershipTokenBuffer,
                    pResponseInfo->u.acceptedResponse.pCertOwnershipToken,
                    pResponseInfo->u.acceptedResponse.ownershipTokenLength );
            /* Add a NULL terminator to the buffer (to treat the buffer as a string!) */
            *( certIdTokenContext->pOwnershipTokenBuffer + pResponseInfo->u.acceptedResponse.ownershipTokenLength ) = '\0';
        }

        /* Print the received credentials information.*/
        IotLogInfo( "Server has accepted Certificate-Signing Request: "
                    "\nCertificate PEM={%.*s}\nCertificate ID={%.*s}\nOwnership Token={%.*s}\n",
                    pResponseInfo->u.acceptedResponse.deviceCertLength,
                    pResponseInfo->u.acceptedResponse.pDeviceCert,
                    pResponseInfo->u.acceptedResponse.certIdLength,
                    pResponseInfo->u.acceptedResponse.pCertId,
                    pResponseInfo->u.acceptedResponse.ownershipTokenLength,
                    pResponseInfo->u.acceptedResponse.pCertOwnershipToken );
    }
    else
    {
        IotLogWarn( "Oops, certificate creation from CSR has been rejected. "
                    "Please verify that the IoT Policy attached to the demo credentials "
                    "allows the \"iot:CreateCertificateFromCsr\" action." );
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
        IotLogInfo( "Oops, server rejected request for provisioning the demo app. "
                    "Please verify that the IoT Policy attached to the demo credentials "
                    "allows the \"iot:RegisterThing\" action." );
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
 * @brief The function that runs the Provisioning demo, for the AWS IoT generated
 * certificate from device generated CSR use-case, called by the demo runner.
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
int RunProvisioningWithCsrDemo( bool awsIotMqttMode,
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
    AwsIotProvisioningCreateCertFromCsrCallbackInfo_t certFromCsrCallback =
        AWS_IOT_PROVISIONING_CREATE_CERTIFICATE_FROM_CSR_CALLBACK_INFO_INITIALIZER;
    AwsIotProvisioningRegisterThingCallbackInfo_t registerThingResponseCallback =
        AWS_IOT_PROVISIONING_REGISTER_THING_CALLBACK_INFO_INITIALIZER;

    /* Represents memory that will be allocated to store the Certificate ID that will be provided by the credential
     * requesting API through the callback. */
    _demoCertFromCsrCallbackContext_t newCertificateDataContext;

    newCertificateDataContext.pCertificateIdBuffer = NULL;
    newCertificateDataContext.certificateIdLength = 0;
    newCertificateDataContext.pOwnershipTokenBuffer = NULL;
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

    /* The list of parameters that will be used as "context" for provisioning the demo application.
     * This demo will pass exactly 2 different parameter entries for requesting provisioning. */
    AwsIotProvisioningRequestParameterEntry_t provisioningParameters[ 2 ] = { { 0 } };

    /* Determine if a provisioning template name has been specified. */
    if( ( ( void * ) pTemplateName == NULL ) || ( strlen( pTemplateName ) == 0 ) )
    {
        IotLogError( "A valid provisioning template name must be provided." );
        status = EXIT_FAILURE;
    }

    /* Generate the list of parameters to send for provisioning */
    if( status != EXIT_FAILURE )
    {
        if( ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME == NULL ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME_LENGTH == 0 ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE == NULL ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE_LENGTH == 0 ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME == NULL ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME_LENGTH == 0 ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE == NULL ) ||
            ( AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE_LENGTH == 0 ) )
        {
            IotLogError( "The provisioning demo requires 2 pairs of name and value data for parameters to be configured." );
            status = EXIT_FAILURE;
        }
        else
        {
            provisioningParameters[ 0 ].pParameterKey = AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME;
            provisioningParameters[ 0 ].parameterKeyLength = AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_NAME_LENGTH;
            provisioningParameters[ 0 ].pParameterValue = AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE;
            provisioningParameters[ 0 ].parameterValueLength = AWS_IOT_DEMO_PROVISIONING_PARAMETER_SERIAL_NUMBER_VALUE_LENGTH;
            provisioningParameters[ 1 ].pParameterKey = AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME;
            provisioningParameters[ 1 ].parameterKeyLength = AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_NAME_LENGTH;
            provisioningParameters[ 1 ].pParameterValue = AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE;
            provisioningParameters[ 1 ].parameterValueLength = AWS_IOT_DEMO_PROVISIONING_PARAMETER_2_VALUE_LENGTH;
        }
    }

    if( status != EXIT_FAILURE )
    {
        /* Determine the length of the client ID Name. */
        if( pIdentifier != NULL )
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
        certFromCsrCallback.userParam = &newCertificateDataContext;

        /* Set the callback function for handling device credentials that the server will send. */
        certFromCsrCallback.function = _demoCertFromCsrCallback;

        /* Call the API to get new device credentials for this demo, and check that the certificate ID data is populated. */
        requestStatus = AwsIotProvisioning_CreateCertificateFromCsr( mqttConnection,
                                                                     IOT_MQTT_QOS_1,
                                                                     AWS_IOT_DEMO_PROVISIONING_CSR_PEM,
                                                                     strlen( AWS_IOT_DEMO_PROVISIONING_CSR_PEM ),
                                                                     AWS_IOT_DEMO_PROVISIONING_TIMEOUT_PERIOD_MS,
                                                                     &certFromCsrCallback );

        if( requestStatus != AWS_IOT_PROVISIONING_SUCCESS )
        {
            status = EXIT_FAILURE;
            IotLogError( "Request to get new credentials failed, error %s ",
                         AwsIotProvisioning_strerror( requestStatus ) );
        }
        else if( ( newCertificateDataContext.pCertificateIdBuffer == NULL ) ||
                 ( newCertificateDataContext.pOwnershipTokenBuffer == NULL ) )
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
        requestInfo.pCertificateOwnershipToken = newCertificateDataContext.pOwnershipTokenBuffer;
        requestInfo.ownershipTokenLength = newCertificateDataContext.tokenLength;
        requestInfo.pTemplateName = AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME;
        requestInfo.templateNameLength = sizeof( AWS_IOT_DEMO_PROVISIONING_TEMPLATE_NAME ) - 1;
        requestInfo.pParametersStart = provisioningParameters;
        requestInfo.numOfParameters = sizeof( provisioningParameters ) / sizeof( AwsIotProvisioningRequestParameterEntry_t );

        /* Set the callback function for handling device credentials that the server will send. */
        registerThingResponseCallback.function = _demoRegisterThingCallback;

        /* Call the API to provision the demo application with the certificate ID that we received, and the template
         * name associated with the demo endpoint account. */
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
    if( newCertificateDataContext.pOwnershipTokenBuffer != NULL )
    {
        Iot_DefaultFree( newCertificateDataContext.pOwnershipTokenBuffer );
    }

    return status;
}

/*-----------------------------------------------------------*/
