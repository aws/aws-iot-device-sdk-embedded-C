/*
 * AWS IoT Device SDK for Embedded C 202412.00
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

/* Standard includes. */
#include <assert.h>
#include <time.h>
#include <stdlib.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Demo S3 utils header. */
#include "http_demo_s3_utils.h"

/* MBEDTLS API header. */
#include "mbedtls/sha256.h"
#include "mbedtls/compat-2.x.h"

/* OpenSSL transport header. */
#include "openssl_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief The URI path for HTTP requests to AWS IoT Credential provider.
 */
#define AWS_IOT_CREDENTIAL_PROVIDER_URI_PATH \
    "/role-aliases/"                         \
    AWS_IOT_CREDENTIAL_PROVIDER_ROLE "/credentials"

/**
 * @brief HTTP header name for specifying the IOT Thing resource name in request to AWS S3.
 */
#define AWS_IOT_THING_NAME_HEADER_FIELD               "x-amzn-iot-thingname"

/**
 * @brief Field name of the HTTP date header to read from the AWS IOT credential provider server response.
 */
#define AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER    "date"

/**
 * @brief Access Key Id key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY        "credentials.accessKeyId"

/**
 * @brief Secret Access key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY        "credentials.secretAccessKey"

/**
 * @brief Session Token key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY        "credentials.sessionToken"

/**
 * @brief Expiration Date key to be searched in the IoT credentials response.
 */
#define CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY      "credentials.expiration"

/*-----------------------------------------------------------*/

/**
 * @brief The host address string extracted from the AWS IOT CREDENTIAL PROVIDER URL.
 *
 * @note SERVER_HOST_NAME_MAX_LENGTH is set as the array length here as the
 * length of the host name string cannot exceed this value.
 */
char serverHost[ SERVER_HOST_NAME_MAX_LENGTH ];

/**
 * @brief The length of the host address found in the the AWS IOT CREDENTIAL PROVIDER URL.
 */
size_t serverHostLength;

/**
 * @brief The security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
const char * pSecurityToken;

/**
 * @brief Length of security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
size_t securityTokenLen;

/**
 * @brief The expiration time for the temporary credentials retrieved
 * from AWS IoT credential provider service.
 */
const char * pExpiration;

/**
 * @brief Length of expiration time for the temporary credentials retrieved
 * from AWS IoT credential provider service.
 */
size_t expirationLen;

/*-----------------------------------------------------------*/

/**
 * @brief Parse the credentials retrieved from AWS IOT Credential Provider using coreJSON API.
 *
 * @param[in] response HTTP response which needs to be parsed to get the credentials.
 * @param[out] sigvCreds Buffer passed to store the parsed credentials.
 *
 * @return #JSONSuccess if the credentials are parsed successfully;
 * #JSONNullParameter if any pointer parameters are NULL;
 * #JSONBadParameter if any of the response parameters that needs to be parsed are empty;
 * #JSONNotFound if the key to be parsed is not in the response.
 */
static JSONStatus_t parseCredentials( HTTPResponse_t * response,
                                      SigV4Credentials_t * sigvCreds );

/*-----------------------------------------------------------*/

bool getTemporaryCredentials( TransportInterface_t * transportInterface,
                              char * pDateISO8601,
                              size_t pDateISO8601Len,
                              HTTPResponse_t * response,
                              SigV4Credentials_t * sigvCreds )
{
    bool returnStatus = true;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    size_t pathLen = 0;
    size_t addressLen = 0;
    HTTPStatus_t httpStatus = HTTPSuccess;
    SigV4Status_t sigv4Status = SigV4Success;
    JSONStatus_t jsonStatus = JSONSuccess;
    const char * pAddress = NULL;
    const char * pDate = NULL;
    const char * pPath = NULL;
    size_t dateLen = 0;

    assert( transportInterface != NULL );
    assert( response != NULL );
    assert( sigvCreds != NULL );
    assert( pDateISO8601 != NULL );
    assert( pDateISO8601Len > 0 );

    pAddress = AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT;
    addressLen = strlen( AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT );

    pPath = AWS_IOT_CREDENTIAL_PROVIDER_URI_PATH;
    pathLen = strlen( AWS_IOT_CREDENTIAL_PROVIDER_URI_PATH );

    /* Initialize Request header buffer. */
    requestHeaders.pBuffer = response->pBuffer;
    requestHeaders.bufferLen = response->bufferLen;

    /* Set HTTP request parameters to get temporary AWS IoT credentials. */
    requestInfo.pMethod = HTTP_METHOD_GET;
    requestInfo.methodLen = sizeof( HTTP_METHOD_GET ) - 1;
    requestInfo.pPath = pPath;
    requestInfo.pathLen = pathLen;
    requestInfo.pHost = pAddress;
    requestInfo.hostLen = addressLen;
    requestInfo.reqFlags = 0;

    response->pHeaderParsingCallback = NULL;

    if( returnStatus == true )
    {
        /* Initialize request headers. */
        httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );

        if( httpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to initialize request headers: Error=%s.",
                        HTTPClient_strerror( httpStatus ) ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        /* Add AWS_IOT_THING_NAME_HEADER_FIELD header to the HTTP request headers. */
        httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                           AWS_IOT_THING_NAME_HEADER_FIELD,
                                           sizeof( AWS_IOT_THING_NAME_HEADER_FIELD ) - 1U,
                                           AWS_IOT_THING_NAME,
                                           sizeof( AWS_IOT_THING_NAME ) - 1U );

        if( httpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add x-amz-iot-thing-name header to request headers: Error=%s.",
                        HTTPClient_strerror( httpStatus ) ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        /* Send the request to AWS IoT Credentials Provider to obtain temporary credentials
         * so that the demo application can access configured S3 bucket thereafter. */
        httpStatus = HTTPClient_Send( transportInterface,
                                      &requestHeaders,
                                      NULL,
                                      0,
                                      response, 0 );

        if( httpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to send HTTP GET request to %s%s  for obtaining temporary credentials: Error=%s.",
                        pAddress, pPath, HTTPClient_strerror( httpStatus ) ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        /* Parse the credentials received in the response. */
        jsonStatus = parseCredentials( response, sigvCreds );

        LogDebug( ( "AWS IoT credential provider response: %.*s.",
                    ( int32_t ) response->bufferLen, response->pBuffer ) );

        if( jsonStatus != JSONSuccess )
        {
            LogError( ( "Failed to parse temporary IoT credentials retrieved from AWS IoT credential provider" ) );
            returnStatus = false;
        }
    }

    /* Get the AWS IoT date from the http response. */
    if( returnStatus == true )
    {
        httpStatus = HTTPClient_ReadHeader( response,
                                            AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER,
                                            sizeof( AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER ) - 1,
                                            ( const char ** ) &pDate,
                                            &dateLen );

        if( httpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to retrieve \"%s\" header from response: Error=%s.",
                        AWS_IOT_CRED_PROVIDER_RESPONSE_DATE_HEADER, HTTPClient_strerror( httpStatus ) ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        /* Convert AWS IoT date retrieved from IoT server to ISO 8601 date format. */
        sigv4Status = SigV4_AwsIotDateToIso8601( pDate, dateLen, pDateISO8601, pDateISO8601Len );

        if( sigv4Status != SigV4Success )
        {
            LogError( ( "Failed to convert AWS IoT date to ISO 8601 format." ) );
            returnStatus = false;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

int32_t sha256( const char * pInput,
                size_t ilen,
                char * pOutput )
{
    return mbedtls_sha256_ret( ( const unsigned char * ) pInput, ilen, ( unsigned char * ) pOutput, 0 );
}

/*-----------------------------------------------------------*/

int32_t sha256Init( void * hashContext )
{
    mbedtls_sha256_init( ( mbedtls_sha256_context * ) hashContext );
    return mbedtls_sha256_starts_ret( ( mbedtls_sha256_context * ) hashContext, 0 );
}

/*-----------------------------------------------------------*/

int32_t sha256Update( void * hashContext,
                      const uint8_t * pInput,
                      size_t inputLen )
{
    return mbedtls_sha256_update_ret( ( mbedtls_sha256_context * ) hashContext,
                                      ( const unsigned char * ) pInput,
                                      inputLen );
}

/*-----------------------------------------------------------*/

int32_t sha256Final( void * hashContext,
                     uint8_t * pOutput,
                     size_t outputLen )
{
    assert( outputLen >= SHA256_HASH_DIGEST_LENGTH );

    ( void ) outputLen;

    return mbedtls_sha256_finish_ret( ( mbedtls_sha256_context * ) hashContext,
                                      ( unsigned char * ) pOutput );
}

/*-----------------------------------------------------------*/

int32_t connectToIotServer( NetworkContext_t * pNetworkContext )
{
    int32_t returnStatus = EXIT_SUCCESS;
    /* Variable to store Host Address of AWS IoT Credential Provider server. */
    const char * pAddress = NULL;

    /* Status returned by OpenSSL transport implementation. */
    OpensslStatus_t opensslStatus;
    /* Credentials to establish the TLS connection. */
    OpensslCredentials_t opensslCredentials = { 0 };
    /* Information about the server to send the HTTP requests. */
    ServerInfo_t serverInfo = { 0 };

    pAddress = AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT;
    serverHostLength = strlen( AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT );

    if( returnStatus == EXIT_SUCCESS )
    {
        memcpy( serverHost, pAddress, serverHostLength );
        serverHost[ serverHostLength ] = '\0';

        /* Initialize TLS credentials. */
        opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
        opensslCredentials.sniHostName = serverHost;
        opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
        opensslCredentials.pPrivateKeyPath = CLIENT_PRIVATE_KEY_PATH;

        /* Initialize server information. */
        serverInfo.pHostName = serverHost;
        serverInfo.hostNameLength = serverHostLength;
        serverInfo.port = HTTPS_PORT;

        /* Establish a TLS session with the HTTP server. This example connects
         * to the AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT and HTTPS_PORT in
         * demo_config.h. */
        LogInfo( ( "Establishing a TLS session with %s:%d.",
                   serverHost,
                   HTTPS_PORT ) );

        opensslStatus = Openssl_Connect( pNetworkContext,
                                         &serverInfo,
                                         &opensslCredentials,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS );

        returnStatus = ( opensslStatus == OPENSSL_SUCCESS ) ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static JSONStatus_t parseCredentials( HTTPResponse_t * response,
                                      SigV4Credentials_t * sigvCreds )
{
    JSONStatus_t jsonStatus = JSONSuccess;

    assert( response != NULL );
    assert( sigvCreds != NULL );

    if( jsonStatus == JSONSuccess )
    {
        /* Get accessKeyId from HTTP response. */
        jsonStatus = JSON_Search( ( char * ) response->pBody,
                                  response->bodyLen,
                                  CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY,
                                  strlen( CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY ),
                                  ( char ** ) &( sigvCreds->pAccessKeyId ),
                                  &( sigvCreds->accessKeyIdLen ) );

        if( jsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing accessKeyId in the credentials." ) );
        }
    }

    if( jsonStatus == JSONSuccess )
    {
        /* Get secretAccessKey from HTTP response. */
        jsonStatus = JSON_Search( ( char * ) response->pBody,
                                  response->bodyLen,
                                  CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY,
                                  strlen( CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY ),
                                  ( char ** ) &( sigvCreds->pSecretAccessKey ),
                                  &( sigvCreds->secretAccessKeyLen ) );

        if( jsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing secretAccessKey in the credentials." ) );
        }
    }

    if( jsonStatus == JSONSuccess )
    {
        /* Get sessionToken from HTTP response. */
        jsonStatus = JSON_Search( ( char * ) response->pBody,
                                  response->bodyLen,
                                  CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY,
                                  strlen( CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY ),
                                  ( char ** ) &( pSecurityToken ),
                                  &( securityTokenLen ) );

        if( jsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing sessionToken in the credentials." ) );
        }
    }

    if( jsonStatus == JSONSuccess )
    {
        /* Get expiration date from HTTP response. */
        jsonStatus = JSON_Search( ( char * ) response->pBody,
                                  response->bodyLen,
                                  CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY,
                                  strlen( CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY ),
                                  ( char ** ) &( pExpiration ),
                                  &( expirationLen ) );

        if( jsonStatus != JSONSuccess )
        {
            LogError( ( "Error parsing expiration date in the credentials." ) );
        }
        else
        {
            LogInfo( ( "AWS IoT credentials will expire after this timestamp: %.*s.", ( int ) expirationLen, pExpiration ) );
        }
    }

    return jsonStatus;
}

/*-----------------------------------------------------------*/
