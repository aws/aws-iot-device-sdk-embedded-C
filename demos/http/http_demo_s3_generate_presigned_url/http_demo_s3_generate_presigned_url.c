/*
 * AWS IoT Device SDK for Embedded C 202211.00
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
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/* HTTP API header. */
#include "core_http_client.h"

/* JSON API header. */
#include "core_json.h"

/* SIGV4 API header. */
#include "sigv4.h"

/* MBEDTLS API header. */
#include "mbedtls/sha256.h"

/* OpenSSL transport header. */
#include "openssl_posix.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/* Check that TLS port of the server is defined. */
#ifndef HTTPS_PORT
    #error "Please define the HTTPS_PORT macro in demo_config.h ."
#endif

/* Check that a path for Root CA Certificate is defined. */
#ifndef ROOT_CA_CERT_PATH
    #error "Please define the ROOT_CA_CERT_PATH macro in demo_config.h."
#endif

/* Check that transport timeout for transport send and receive is defined. */
#ifndef TRANSPORT_SEND_RECV_TIMEOUT_MS
    #define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 4096 )
#endif

/* Check that AWS IOT Thing Name is defined. */
#ifndef AWS_IOT_THING_NAME
    #error "Please define the AWS_IOT_THING_NAME macro in demo_config.h."
#endif

/* Check that AWS IOT credential provider endpoint is defined. */
#ifndef AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT
    #error "Please define the AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT macro in demo_config.h."
#endif

/* Check that AWS IOT credential provider role is defined. */
#ifndef AWS_IOT_CREDENTIAL_PROVIDER_ROLE
    #error "Please define the AWS_IOT_CREDENTIAL_PROVIDER_ROLE macro in demo_config.h."
#endif

/* Check that AWS S3 BUCKET NAME is defined. */
#ifndef AWS_S3_BUCKET_NAME
    #error "Please define the AWS_S3_BUCKET_NAME macro in demo_config.h."
#endif

/* Check that AWS S3 OBJECT NAME is defined. */
#ifndef AWS_S3_OBJECT_NAME
    #error "Please define the AWS_S3_OBJECT_NAME macro in demo_config.h."
#endif

/* Check that AWS S3 BUCKET REGION is defined. */
#ifndef AWS_S3_BUCKET_REGION
    #error "Please define the AWS_S3_BUCKET_REGION macro in which bucket resides in demo_config.h."
#endif

/**
 * @brief The length of the HTTP GET method.
 */
#define HTTP_METHOD_GET_LENGTH                    ( sizeof( HTTP_METHOD_GET ) - 1 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef HTTP_MAX_DEMO_LOOP_COUNT
    #define HTTP_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in seconds to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S    ( 5 )

/**
 * @brief Buffer Length for storing the AWS IoT Credentials retrieved from
 * AWS IoT credential provider which includes the following:
 * 1. Access Key ID
 * 2. Secret Access key
 * 3. Session Token
 * 4. Expiration Date
 */
#define CREDENTIAL_BUFFER_LENGTH                 1500U

/**
 * @brief AWS Service name to send HTTP request using SigV4 library.
 */
#define AWS_S3_SERVICE_NAME                      "s3"

/**
 * @brief AWS S3 Endpoint.
 */
#define AWS_S3_ENDPOINT                            \
    AWS_S3_BUCKET_NAME "." AWS_S3_SERVICE_NAME "." \
    AWS_S3_BUCKET_REGION  ".amazonaws.com"

/**
 * @brief AWS S3 URI PATH.
 */
#define AWS_S3_URI_PATH \
    "/" AWS_S3_OBJECT_NAME

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
 * @brief Length of AWS HTTP Authorization header value generated using SigV4 library.
 */
#define AWS_HTTP_AUTH_HEADER_VALUE_LEN                2048U

/**
 * @brief Maximum Length for AWS IOT Credential provider server host name.
 *
 * @note length of the AWS IOT Credential provider server host name string
 * cannot exceed this value.
 */
#define SERVER_HOST_NAME_MAX_LENGTH                   65U

/**
 * @brief Length in bytes of hex encoded hash digest.
 */
#define HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH         ( ( ( uint16_t ) 64 ) )

/**
 * @brief Length in bytes of SHA256 hash digest.
 */
#define SHA256_HASH_DIGEST_LENGTH                     ( HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH / 2 )

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

/**
 * @brief Represents empty payload for HTTP GET request sent to AWS S3.
 */
#define S3_REQUEST_EMPTY_PAYLOAD                      ""


/**
 * @brief A buffer used in the demo for storing HTTP request headers and HTTP
 * response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can decide how
 * to use buffers to store HTTP requests and responses.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/**
 * @brief Represents header data that will be sent in an HTTP request.
 */
static HTTPRequestHeaders_t requestHeaders;

/**
 * @brief Configurations of the initial request headers that are passed to
 * #HTTPClient_InitializeRequestHeaders.
 */
static HTTPRequestInfo_t requestInfo;

/**
 * @brief Represents a response returned from an HTTP server.
 */
static HTTPResponse_t response;

/**
 * @brief The host address string extracted from the AWS IOT CREDENTIAL PROVIDER URL.
 *
 * @note SERVER_HOST_NAME_MAX_LENGTH is set as the array length here as the
 * length of the host name string cannot exceed this value.
 */
static char serverHost[ SERVER_HOST_NAME_MAX_LENGTH ];

/**
 * @brief The length of the host address found in the the AWS IOT CREDENTIAL PROVIDER URL.
 */
static size_t serverHostLength;

/**
 * @brief The location of the path within the server URL.
 */
static const char * pPath;

/**
 *  @brief mbedTLS Hash Context passed to SigV4 cryptointerface for generating the hash digest.
 */
static mbedtls_sha256_context hashContext = { 0 };

/**
 *  @brief Configurations of the AWS credentials sent to sigV4 library for generating the Authorization Header.
 */
static SigV4Credentials_t sigvCreds = { 0 };

/**
 * @brief Represents a response returned from an AWS IOT credential provider.
 */
static HTTPResponse_t credentialResponse = { 0 };

/**
 * @brief Buffer used in the demo for storing temporary credentials
 * received from AWS TOT credential provider.
 */
static uint8_t pAwsIotHttpBuffer[ CREDENTIAL_BUFFER_LENGTH ] = { 0 };

/**
 * @brief Represents date in ISO8601 format used in the HTTP requests sent to AWS S3.
 */
static char pDateISO8601[ SIGV4_ISO_STRING_LEN ] = { 0 };

/**
 * @brief Represents hash digest of payload.
 */
static char pPayloadHashDigest[ SHA256_HASH_DIGEST_LENGTH ];

/**
 * @brief Represents Authorization header value generated using SigV4 library.
 */
static char pSigv4Auth[ AWS_HTTP_AUTH_HEADER_VALUE_LEN ];

/**
 * @brief Represents Length of Authorization header value generated using SigV4 library.
 */
static size_t sigv4AuthLen = AWS_HTTP_AUTH_HEADER_VALUE_LEN;

/**
 * @brief The security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
static const char * pSecurityToken;

/**
 * @brief Length of security token retrieved from AWS IoT credential provider
 * required for making HTTP requests to AWS S3.
 */
static size_t securityTokenLen;

/**
 * @brief The expiration time for the temporary credentials retrieved
 * from AWS IoT credential provider service.
 */
static const char * pExpiration;

/**
 * @brief Length of expiration time for the temporary credentials retrieved
 * from AWS IoT credential provider service.
 */
static size_t expirationLen;

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Connect to AWS IOT Credential Provider server with reconnection retries.
 *
 * @param[out] pNetworkContext The output parameter to return the created
 * network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int32_t connectToIotServer( NetworkContext_t * pNetworkContext );

/**
 * @brief Send multiple HTTP GET requests, based on a specified path, to
 * download a file in chunks from the host S3 server.
 *
 * @param[in] pTransportInterface The transport interface for making network
 * calls.
 * @param[in] pPath The Request-URI to the objects of interest. This string
 * should be null-terminated.
 *
 * @return The status of the file download using multiple GET requests to the
 * server: true on success, false on failure.
 */
static bool downloadS3ObjectFile( const TransportInterface_t * pTransportInterface,
                                  const char * pPath );

/**
 * @brief Retrieve the size of the S3 object that is specified in pPath.
 *
 * @param[out] pFileSize The size of the S3 object.
 * @param[in] pTransportInterface The transport interface for making network
 * calls.
 * @param[in] pHost The server host address.
 * @param[in] hostLen The length of the server host address.
 * @param[in] pPath The Request-URI to the objects of interest. This string
 * should be null-terminated.
 *
 * @return The status of the file size acquisition using a GET request to the
 * server: true on success, false on failure.
 */
static bool getS3ObjectFileSize( size_t * pFileSize,
                                 const TransportInterface_t * pTransportInterface,
                                 const char * pHost,
                                 size_t hostLen,
                                 const char * pPath );

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

/**
 * @brief Retrieve the temporary credentials from AWS IOT Credential Provider.
 *
 * @param[in] pTransportInterface The transport interface for performing network send/recv operations.
 * @param[out] pDateISO8601 Buffer to store the ISO8601 formatted date.
 * @param[in] pDateISO8601Len Length of the buffer provided to store ISO8601 formatted date.
 * @param[in,out] response Response buffer to store the HTTP response received.
 * @param[out] sigvCreds Buffer to store the parsed credentials.
 *
 * @return `true` if credentials are retrieved successfully otherwise 'false`.
 */
static bool getTemporaryCredentials( TransportInterface_t * transportInterface,
                                     char * pDateISO8601,
                                     size_t pDateISO8601Len,
                                     HTTPResponse_t * response,
                                     SigV4Credentials_t * sigvCreds );

/**
 * @brief Get the starting location of HTTP header in an HTTP request.
 *
 * @param[in] requestHeaders HTTP request headers that contains the HTTP request information.
 * @param[out] pStartHeaderLoc Buffer to store the start Location of the HTTP header.
 * @param[out] pHeadersDataLen Length of @p pStartHeaderLoc.
 */
static void getHeaderStartLocFromHttpRequest( HTTPRequestHeaders_t requestHeaders,
                                              char ** pStartHeaderLoc,
                                              size_t * pHeadersDataLen );

/**
 * @brief Calculate SHA256 digest.
 *
 * @param[in] pInput Input string to hash.
 * @param[in] ilen Length of input string.
 * @param[out] pOutput Buffer to store the generated hash.
 */
static int32_t sha256( const char * pInput,
                       size_t ilen,
                       char * pOutput );

/**
 * @brief Application-defined Hash Initialization function provided
 * to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
static int32_t sha256Init( void * hashContext );

/**
 * @brief Application-defined Hash Update function provided to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
static int32_t sha256Update( void * hashContext,
                             const uint8_t * pInput,
                             size_t inputLen );

/**
 * @brief Application-defined Hash Final function provided to the SigV4 library.
 *
 * @note Refer to SigV4CryptoInterface_t interface documentation for this function.
 */
static int32_t sha256Final( void * hashContext,
                            uint8_t * pOutput,
                            size_t outputLen );

/**
 * @brief CryptoInterface provided to SigV4 library for generating the hash digest.
 */
static SigV4CryptoInterface_t cryptoInterface =
{
    .hashInit      = sha256Init,
    .hashUpdate    = sha256Update,
    .hashFinal     = sha256Final,
    .pHashContext  = &hashContext,
    .hashBlockLen  = HEX_ENCODED_SHA256_HASH_DIGEST_LENGTH,
    .hashDigestLen = SHA256_HASH_DIGEST_LENGTH,
};

/**
 * @brief SigV4 parameters provided to SigV4 library by the application for generating
 * the Authorization header.
 */
static SigV4Parameters_t sigv4Params =
{
    .pCredentials     = &sigvCreds,
    .pDateIso8601     = pDateISO8601,
    .pRegion          = AWS_S3_BUCKET_REGION,
    .regionLen        = sizeof( AWS_S3_BUCKET_REGION ) - 1,
    .pService         = AWS_S3_SERVICE_NAME,
    .serviceLen       = sizeof( AWS_S3_SERVICE_NAME ) - 1,
    .pCryptoInterface = &cryptoInterface,
    .pHttpParameters  = NULL
};

/*-----------------------------------------------------------*/

static bool getTemporaryCredentials( TransportInterface_t * transportInterface,
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
            LogError( ( "Error parsing %s in the credentials.\n%s", CREDENTIALS_RESPONSE_ACCESS_KEY_ID_KEY, response->pBody ) );
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
            LogError( ( "Error parsing %s in the credentials.\n%s", CREDENTIALS_RESPONSE_SECRET_ACCESS_KEY, response->pBody ) );
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
            LogError( ( "Error parsing %s in the credentials.\n%s", CREDENTIALS_RESPONSE_SESSION_TOKEN_KEY, response->pBody ) );
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
            LogError( ( "Error parsing %s in the credentials.\n%s", CREDENTIALS_RESPONSE_EXPIRATION_DATE_KEY, response->pBody ) );
        }
        else
        {
            LogInfo( ( "AWS IoT credentials will expire after this timestamp: %.*s.", ( int ) expirationLen, pExpiration ) );
        }
    }

    return jsonStatus;
}

/*-----------------------------------------------------------*/

static int32_t sha256( const char * pInput,
                       size_t ilen,
                       char * pOutput )
{
    return mbedtls_sha256_ret( ( const unsigned char * ) pInput, ilen, ( unsigned char * ) pOutput, 0 );
}

/*-----------------------------------------------------------*/

static int32_t sha256Init( void * hashContext )
{
    mbedtls_sha256_init( ( mbedtls_sha256_context * ) hashContext );
    return mbedtls_sha256_starts_ret( ( mbedtls_sha256_context * ) hashContext, 0 );
}

/*-----------------------------------------------------------*/

static int32_t sha256Update( void * hashContext,
                             const uint8_t * pInput,
                             size_t inputLen )
{
    return mbedtls_sha256_update_ret( ( mbedtls_sha256_context * ) hashContext,
                                      ( const unsigned char * ) pInput,
                                      inputLen );
}

/*-----------------------------------------------------------*/

static int32_t sha256Final( void * hashContext,
                            uint8_t * pOutput,
                            size_t outputLen )
{
    assert( outputLen >= SHA256_HASH_DIGEST_LENGTH );

    ( void ) outputLen;

    return mbedtls_sha256_finish_ret( ( mbedtls_sha256_context * ) hashContext,
                                      ( unsigned char * ) pOutput );
}

static void getHeaderStartLocFromHttpRequest( HTTPRequestHeaders_t requestHeaders,
                                              char ** pStartHeaderLoc,
                                              size_t * pHeadersDataLen )
{
    size_t headerLen = requestHeaders.headersLen;
    char * pHeaders = ( char * ) requestHeaders.pBuffer;
    bool newLineFound = false;

    assert( pStartHeaderLoc != NULL );
    assert( pHeadersDataLen != NULL );

    while( headerLen >= 2 )
    {
        if( 0 == strncmp( pHeaders, "\r\n", strlen( "\r\n" ) ) )
        {
            newLineFound = true;
            break;
        }

        pHeaders++;
        headerLen--;
    }

    if( newLineFound == false )
    {
        LogError( ( "Failed to find starting location of HTTP headers in HTTP request: \"\\r\\n\" missing before start of HTTP headers." ) );
    }

    assert( newLineFound != false );

    /* Moving header pointer past "\r\n" .*/
    *pHeadersDataLen = headerLen - 2;
    *pStartHeaderLoc = pHeaders + 2;
}

/*-----------------------------------------------------------*/

static int32_t connectToIotServer( NetworkContext_t * pNetworkContext )
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

static bool downloadS3ObjectFile( const TransportInterface_t * pTransportInterface,
                                  const char * pPath )
{
    bool returnStatus = false;
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* The size of the file we are trying to download in S3. */
    size_t fileSize = 0;

    /* The number of bytes we want to request with in each range of the file
     * bytes. */
    size_t numReqBytes = 0;
    /* curByte indicates which starting byte we want to download next. */
    size_t curByte = 0;

    SigV4Status_t sigv4Status = SigV4Success;
    SigV4HttpParameters_t sigv4HttpParams;

    char * pHeaders = NULL;
    size_t headersLen = 0;

    /* Store Signature used in AWS HTTP requests generated using SigV4 library. */
    char * signature = NULL;
    size_t signatureLen = 0;

    assert( pPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );

    /* Initialize the request object. */
    requestInfo.pHost = serverHost;
    requestInfo.hostLen = serverHostLength;
    requestInfo.pMethod = HTTP_METHOD_GET;
    requestInfo.methodLen = HTTP_METHOD_GET_LENGTH;
    requestInfo.pPath = pPath;
    requestInfo.pathLen = strlen( pPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. This is done in
     * order to download the file in parts. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing request
     * headers is reused here. */
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    /* Verify the file exists by retrieving the file size. */
    returnStatus = getS3ObjectFileSize( &fileSize,
                                        pTransportInterface,
                                        serverHost,
                                        serverHostLength,
                                        pPath );
    return true;
}

/*-----------------------------------------------------------*/

static bool getS3ObjectFileSize( size_t * pFileSize,
                                 const TransportInterface_t * pTransportInterface,
                                 const char * pHost,
                                 size_t hostLen,
                                 const char * pPath )
{
    bool returnStatus = true;
    HTTPStatus_t httpStatus = HTTPSuccess;
    HTTPRequestHeaders_t requestHeaders;
    HTTPRequestInfo_t requestInfo;
    HTTPResponse_t response;
    uint8_t userBuffer[ USER_BUFFER_LENGTH ];

    /* The location of the file size in contentRangeValStr. */
    char * pFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * contentRangeValStr = NULL;
    size_t contentRangeValStrLength = 0;

    SigV4Status_t sigv4Status = SigV4Success;
    SigV4HttpParameters_t sigv4HttpParams;

    char * pHeaders = NULL;
    size_t headersLen = 0;

    /* Store Signature used in AWS HTTP requests generated using SigV4 library. */
    char * signature = NULL;
    size_t signatureLen = 0;

    assert( pHost != NULL );
    assert( pPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );

    /* Initialize the request object. */
    requestInfo.pHost = pHost;
    requestInfo.hostLen = hostLen;
    requestInfo.pMethod = HTTP_METHOD_GET;
    requestInfo.methodLen = sizeof( HTTP_METHOD_GET ) - 1;
    requestInfo.pPath = pPath;
    requestInfo.pathLen = strlen( pPath );

    /* Set "Connection" HTTP header to "no-user-agent"
     * needed for the presigned URL. */
    requestInfo.reqFlags = HTTP_REQUEST_NO_USER_AGENT_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing request
     * headers is reused here. */
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    LogInfo( ( "Getting presigned URL..." ) );

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                      &requestInfo );

    if( httpStatus != HTTPSuccess )
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( httpStatus ) ) );
        returnStatus = false;
    }

    /* Move request header pointer past the initial headers which are added by coreHTTP
     * library and are not required by SigV4 library. */
    getHeaderStartLocFromHttpRequest( requestHeaders, &pHeaders, &headersLen );

    // <your-access-key-id>/<date>/<AWS Region>/<AWS-service>/aws4_request
    char x_amz_credentials[256] = "";
    strncat(x_amz_credentials, sigvCreds.pAccessKeyId, sigvCreds.accessKeyIdLen);
    strcat(x_amz_credentials, "/");
    strncat(x_amz_credentials, pDateISO8601, 8);
    strcat(x_amz_credentials, "/");
    strcat(x_amz_credentials, AWS_S3_BUCKET_REGION);
    strcat(x_amz_credentials, "/s3/aws4_request");
    //LogInfo( ( "x_amz_credentials = '%s'", x_amz_credentials ) );

    // https://docs.aws.amazon.com/AmazonS3/latest/API/sigv4-query-string-auth.html
    char canonical_queries[2048] = "";
    strcat(canonical_queries, "X-Amz-Algorithm=");
    strcat(canonical_queries, SIGV4_AWS4_HMAC_SHA256);
    strcat(canonical_queries, "&X-Amz-Credential=");
    strcat(canonical_queries, x_amz_credentials);
    strcat(canonical_queries, "&X-Amz-Date=");
    strncat(canonical_queries, pDateISO8601, SIGV4_ISO_STRING_LEN);
    strcat(canonical_queries, "&X-Amz-Expires=3600");
    strcat(canonical_queries, "&X-Amz-Security-Token=");
    strncat(canonical_queries, pSecurityToken, securityTokenLen);
    strcat(canonical_queries, "&X-Amz-SignedHeaders=host");

    /* Setup the HTTP parameters. */
    sigv4HttpParams.pHttpMethod = requestInfo.pMethod;
    sigv4HttpParams.httpMethodLen = requestInfo.methodLen;
    /* None of the requests parameters below are pre-canonicalized */
    sigv4HttpParams.flags = SIGV4_HTTP_IS_PRESIGNED_URL;
    sigv4HttpParams.pPath = requestInfo.pPath;
    sigv4HttpParams.pathLen = requestInfo.pathLen;
    sigv4HttpParams.pQuery = canonical_queries;
    sigv4HttpParams.queryLen = strlen(canonical_queries);
    sigv4HttpParams.pHeaders = pHeaders;
    sigv4HttpParams.headersLen = headersLen;
    sigv4HttpParams.pPayload = S3_REQUEST_EMPTY_PAYLOAD;
    sigv4HttpParams.payloadLen = strlen( S3_REQUEST_EMPTY_PAYLOAD );

    /* Initializing sigv4Params with Http parameters required for the HTTP request. */
    sigv4Params.pHttpParameters = &sigv4HttpParams;

    if( returnStatus == true )
    {
        /* Generate HTTP Authorization header using SigV4_GenerateHTTPAuthorization API. */
        sigv4Status = SigV4_GenerateHTTPAuthorization( &sigv4Params, pSigv4Auth, &sigv4AuthLen, &signature, &signatureLen );

        if( sigv4Status != SigV4Success )
        {
            LogError( ( "Failed to generate HTTP AUTHORIZATION Header. " ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        char ota_temp_url[4096] = "https://" AWS_S3_ENDPOINT AWS_S3_URI_PATH "?";
        strcat(ota_temp_url, "X-Amz-Algorithm=");
        strcat(ota_temp_url, SIGV4_AWS4_HMAC_SHA256);
        strcat(ota_temp_url, "&X-Amz-Credential=");
        size_t encodedLen = sizeof(ota_temp_url) - strlen(ota_temp_url);
        returnStatus = SigV4_EncodeURI( x_amz_credentials,
                                        strlen(x_amz_credentials),
                                        ota_temp_url + strlen(ota_temp_url),
                                        &encodedLen,
                                        true/* encode slash */,
                                        false/* do not double encode equal */ );
        if( returnStatus != SigV4Success )
        {
            LogError( ( "Failed to run SigV4_EncodeURI on '%s'.", x_amz_credentials ) );
        }
        strcat(ota_temp_url, "&X-Amz-Date=");
        strncat(ota_temp_url, pDateISO8601, SIGV4_ISO_STRING_LEN);
        strcat(ota_temp_url, "&X-Amz-Expires=3600");
        strcat(ota_temp_url, "&X-Amz-SignedHeaders=host");
        strcat(ota_temp_url, "&X-Amz-Security-Token=");
        encodedLen = sizeof(ota_temp_url) - strlen(ota_temp_url);
        returnStatus = SigV4_EncodeURI( pSecurityToken,
                                        securityTokenLen,
                                        ota_temp_url + strlen(ota_temp_url),
                                        &encodedLen,
                                        true/* encode slash */,
                                        false/* do not double encode equal */ );
        if( returnStatus != SigV4Success )
        {
            LogError( ( "Failed to run SigV4_EncodeURI on '%s'.", pSecurityToken ) );
        }
        strcat(ota_temp_url, "&X-Amz-Signature=");
        strncat(ota_temp_url, signature, signatureLen);
        LogInfo( ( "ota_temp_url=\n%s", ota_temp_url ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example, using a pre-signed URL,  resolves a S3 domain, establishes a
 * TCP connection, validates the server's certificate using the root CA
 * certificate defined in the config header, then finally performs a TLS
 * handshake with the HTTP server so that all communication is encrypted. After
 * which, the HTTP Client library API is used to download the S3 file (by
 * sending multiple GET requests, filling up the response buffer each time until
 * all parts are downloaded). If any request fails, an error code is returned.
 *
 * @note This example is single-threaded and uses statically allocated memory.
 *
 * @note This demo requires user-generated pre-signed URLs to be pasted into
 * demo_config.h. Please use the provided script "presigned_urls_gen.py"
 * (located in located in demos/http/common/src) to generate these URLs. For
 * detailed instructions, see the accompanied README.md.
 *
 * @note If your file requires more than 99 range requests to S3 (depending on
 * the size of the file and the length specified in RANGE_REQUEST_LENGTH), your
 * connection may be dropped by S3. In this case, either increase the buffer
 * size and range request length (if feasible), to reduce the number of requests
 * required, or re-establish the connection with S3 after receiving a
 * "Connection: close" response header.
 */
int main( int argc,
          char ** argv )
{
    /* Return value of main. */
    int32_t returnStatus = EXIT_SUCCESS;
    /* Return value of private functions. */
    bool ret = false, credentialStatus = false;
    int demoRunCount = 0;

    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t transportInterface = { NULL };
    /* The network context for the transport layer interface. */
    NetworkContext_t networkContext;
    OpensslParams_t opensslParams;

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &opensslParams;

    LogInfo( ( "HTTP Client Presigned S3 URL demo using temporary credentials fetched from iot credential provider:\n%s",
               AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT ) );

    /**************************** Connect. ******************************/

    /* Establish TLS connection on top of TCP connection using OpenSSL. */

    /* Attempt to connect to the AWS IOT CREDENTIAL PROVIDER server. If connection fails, retry
     * after a timeout. The timeout value will be exponentially
     * increased until either the maximum number of attempts or the
     * maximum timeout value is reached. The function returns
     * EXIT_FAILURE if the TCP connection cannot be established to the
     * broker after the configured number of attempts. */
    returnStatus = connectToServerWithBackoffRetries( connectToIotServer,
                                                      &networkContext );

    if( returnStatus == EXIT_FAILURE )
    {
        /* Log an error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to AWS IoT CREDENTIAL PROVIDER server %s.",
                    serverHost ) );
    }

    /* Define the transport interface. */
    if( returnStatus == EXIT_SUCCESS )
    {
        ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
        transportInterface.recv = Openssl_Recv;
        transportInterface.send = Openssl_Send;
        transportInterface.pNetworkContext = &networkContext;
    }

    /* Initialize response buffer. */
    credentialResponse.pBuffer = pAwsIotHttpBuffer;
    credentialResponse.bufferLen = CREDENTIAL_BUFFER_LENGTH;

#if 1
    credentialStatus = getTemporaryCredentials( &transportInterface, pDateISO8601, sizeof( pDateISO8601 ), &credentialResponse, &sigvCreds );
#else
    sigvCreds.pAccessKeyId = "ASIAVBKNXEL5KM7WKF5J";
    sigvCreds.accessKeyIdLen = strlen(sigvCreds.pAccessKeyId);
    sigvCreds.pSecretAccessKey = "S96+y1HoKqmKJV+M3rIaqHNiOJfez5Zw7/JKoOMn";
    sigvCreds.secretAccessKeyLen = strlen(sigvCreds.pSecretAccessKey);
    pSecurityToken = "IQoJb3JpZ2luX2VjENn//////////wEaDGV1LWNlbnRyYWwtMSJHMEUCID1N4fp5hf43SfExqAeR0TzAPNPqFN5BB602HNGQgayPAiEAoDmH1Qp9jQxkCw03aEQQgDnoz3wizi7G0YrrP8ZmbIQq5wMI0v//////////ARAAGgwzNDY0NDQ3MzUyMjYiDHcZJJt5/OOrYNMe5Sq7A0Ee9OnHTudb0VfrrPpDa+U4WA2gftulM0TcE5c3d/1CM18/K6RIP47XuG5eLKCWp2mnrs4584LPUB9p3JTzAb8+vqOZJddIgPq6UPo1lzXs8NaRu1AIUvmSeCZESYuzjz52uL0yMvREp+ndOfoesmn7h7ry1QeSvc30Wk48t7jVc/uZXTDrBBbk2oKzcsnFD09Z5XfTAZsCRF/FFxFsLYjpE9I1rreOXB9j43Jw4Sjboa6wb5EViFIlZhyht/qBsgF5yqNuRD/m5Y4z1s4nK9AyEzvclxr53FwrsAlYWD5LSq3QXpeJSuH6eJJcYiwEnPLLjG8XWlFUftzrci9eBa+HWjmN2MxJ87AY2++IMgh5PJlBB0rKAFCFtDMW5e+DWCf/s9HZHeXygXpfk3HW1Z41t24PiJJH0+/8v67bnMmSORb0YZ/qr81mnAbh/CXwyfKVCPDuMLr5prnCE7JRh0MldmS2QT+KHFJBWXsZno1X1Js86zIQO1wOhTYa6vQ6mX3TuPB+ugy/Ihb11a54Fk8snbUc8kVBrr7l/85XPWVap17X8Zz4WQloM+TsUaATFg0Bqa3qoXR+OzgDMKy/36gGOpoBOewB/N92nslpmeMPCK0G8FjdXDsRMGhPjDIbJkfMngM9y/ZNT+ahiQDY8iTUylxxlCec9FvQVs6i5X3vkDVY2pqnQ3L6JnnJ01LIikSMSzvOwuLAgEYin6cgvJ+k8VGNQta4xEFrCDgyZAS3mlyhZ2nqT0fcICwgd9c+gRObVMoonXvISE3CHPuRs5I+MCT1wsDy46rCBSIq6A==";
    securityTokenLen = strlen(pSecurityToken);
    memcpy(pDateISO8601, "20230930T084822Z", sizeof(pDateISO8601));
    credentialStatus = true;
#endif

    returnStatus = ( credentialStatus == true ) ? EXIT_SUCCESS : EXIT_FAILURE;

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Failed to get temporary credentials from AWS IoT CREDENTIALS PROVIDER %s.",
                    serverHost ) );
    }

    /* End the TLS session, then close the TCP connection. */
    ( void ) Openssl_Disconnect( &networkContext );

    if( returnStatus == EXIT_SUCCESS )
    {
        serverHostLength = strlen( AWS_S3_ENDPOINT );
        memcpy( serverHost, AWS_S3_ENDPOINT, serverHostLength );
        serverHost[ serverHostLength ] = '\0';

        /* Define the transport interface. */
        if( returnStatus == EXIT_SUCCESS )
        {
            ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
            transportInterface.recv = Openssl_Recv;
            transportInterface.send = Openssl_Send;
            transportInterface.pNetworkContext = &networkContext;
        }

        /******************** Download S3 Object File. **********************/

        pPath = AWS_S3_URI_PATH;

        if( returnStatus == EXIT_SUCCESS )
        {
            ret = downloadS3ObjectFile( &transportInterface,
                                        pPath );
            returnStatus = ( ret == true ) ? EXIT_SUCCESS : EXIT_FAILURE;
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Log a message indicating an iteration completed successfully. */
        LogInfo( ( "Demo completed successfully." ) );
    }

    return returnStatus;
}
