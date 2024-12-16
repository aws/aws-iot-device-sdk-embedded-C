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
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Common HTTP demo utilities. */
#include "http_demo_s3_utils.h"

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
#define HTTP_METHOD_GET_LENGTH    ( sizeof( HTTP_METHOD_GET ) - 1 )

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
 * @brief Length of AWS HTTP Authorization header value generated using SigV4 library.
 */
#define AWS_HTTP_AUTH_HEADER_VALUE_LEN    2048U

/**
 * @brief Represents empty payload for HTTP GET request sent to AWS S3.
 */
#define S3_REQUEST_EMPTY_PAYLOAD          ""

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
 * @brief Represents Authorization header value generated using SigV4 library.
 */
static char pSigv4Auth[ AWS_HTTP_AUTH_HEADER_VALUE_LEN ];

/**
 * @brief Represents Length of Authorization header value generated using SigV4 library.
 */
static size_t sigv4AuthLen = AWS_HTTP_AUTH_HEADER_VALUE_LEN;

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Generate and print a pre-signed URL to the S3 object file that is specified in pPath.
 *
 *
 * @param[in] pHost The server host address.
 * @param[in] hostLen The length of the server host address.
 * @param[in] pPath The Request-URI to the objects of interest. This string
 * should be null-terminated.
 *
 * @return The status of the pre-signed URL generation: true on success, false on failure.
 */
static bool printS3ObjectFilePresignedURL( const char * pHost,
                                           size_t hostLen,
                                           const char * pPath );

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

static bool printS3ObjectFilePresignedURL( const char * pHost,
                                           size_t hostLen,
                                           const char * pPath )
{
    bool returnStatus = true;
    HTTPStatus_t httpStatus = HTTPSuccess;
    HTTPRequestHeaders_t requestHeaders;
    HTTPRequestInfo_t requestInfo;
    HTTPResponse_t response;
    uint8_t userBuffer[ USER_BUFFER_LENGTH ];

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

    int dateOffset = ( sigvCreds.accessKeyIdLen + 1 );
    /* <your-access-key-id>/<date>/<AWS Region>/<AWS-service>/aws4_request */
    char x_amz_credentials[ 256 ] = { 0 };
    strncat( x_amz_credentials, sigvCreds.pAccessKeyId, sigvCreds.accessKeyIdLen );
    strcat( x_amz_credentials, "/" );
    memcpy( x_amz_credentials + dateOffset, pDateISO8601, 8 );
    strcat( x_amz_credentials, "/" );
    strcat( x_amz_credentials, AWS_S3_BUCKET_REGION );
    strcat( x_amz_credentials, "/s3/aws4_request" );

    /* https://docs.aws.amazon.com/AmazonS3/latest/API/sigv4-query-string-auth.html */
    char canonical_queries[ 2048 ] = "";
    strcat( canonical_queries, "X-Amz-Algorithm=" );
    strcat( canonical_queries, SIGV4_AWS4_HMAC_SHA256 );
    strcat( canonical_queries, "&X-Amz-Credential=" );
    strcat( canonical_queries, x_amz_credentials );
    strcat( canonical_queries, "&X-Amz-Date=" );
    strncat( canonical_queries, pDateISO8601, SIGV4_ISO_STRING_LEN );
    strcat( canonical_queries, "&X-Amz-Expires=3600" );
    strcat( canonical_queries, "&X-Amz-Security-Token=" );
    strncat( canonical_queries, pSecurityToken, securityTokenLen );
    strcat( canonical_queries, "&X-Amz-SignedHeaders=host" );

    /* Setup the HTTP parameters. */
    sigv4HttpParams.pHttpMethod = requestInfo.pMethod;
    sigv4HttpParams.httpMethodLen = requestInfo.methodLen;
    /* None of the requests parameters below are pre-canonicalized */
    sigv4HttpParams.flags = SIGV4_HTTP_IS_PRESIGNED_URL;
    sigv4HttpParams.pPath = requestInfo.pPath;
    sigv4HttpParams.pathLen = requestInfo.pathLen;
    sigv4HttpParams.pQuery = canonical_queries;
    sigv4HttpParams.queryLen = strlen( canonical_queries );
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
        char presigned_url[ 4096 ] = "https://" AWS_S3_ENDPOINT AWS_S3_URI_PATH "?";
        strcat( presigned_url, "X-Amz-Algorithm=" );
        strcat( presigned_url, SIGV4_AWS4_HMAC_SHA256 );
        strcat( presigned_url, "&X-Amz-Credential=" );
        size_t encodedLen = sizeof( presigned_url ) - strlen( presigned_url );
        sigv4Status = SigV4_EncodeURI( x_amz_credentials,
                                       strlen( x_amz_credentials ),
                                       presigned_url + strlen( presigned_url ),
                                       &encodedLen,
                                       true /* encode slash */,
                                       false /* do not double encode equal */ );

        if( sigv4Status != SigV4Success )
        {
            LogError( ( "Failed to run SigV4_EncodeURI on '%s'.", x_amz_credentials ) );
            returnStatus = false;
        }

        strcat( presigned_url, "&X-Amz-Date=" );
        strncat( presigned_url, pDateISO8601, SIGV4_ISO_STRING_LEN );
        strcat( presigned_url, "&X-Amz-Expires=3600" );
        strcat( presigned_url, "&X-Amz-SignedHeaders=host" );
        strcat( presigned_url, "&X-Amz-Security-Token=" );
        encodedLen = sizeof( presigned_url ) - strlen( presigned_url );
        sigv4Status = SigV4_EncodeURI( pSecurityToken,
                                       securityTokenLen,
                                       presigned_url + strlen( presigned_url ),
                                       &encodedLen,
                                       true /* encode slash */,
                                       false /* do not double encode equal */ );

        if( sigv4Status != SigV4Success )
        {
            LogError( ( "Failed to run SigV4_EncodeURI on '%s'.", pSecurityToken ) );
            returnStatus = false;
        }

        strcat( presigned_url, "&X-Amz-Signature=" );
        strncat( presigned_url, signature, signatureLen );
        LogInfo( ( "presigned_url=\n%s", presigned_url ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example generates and prints a pre-signed URL to an S3 object file
 * using temporary credentials
 */
int main( int argc,
          char ** argv )
{
    /* Return value of main. */
    int32_t returnStatus = EXIT_SUCCESS;
    /* Return value of private functions. */
    bool ret = false, credentialStatus = false;

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

    credentialStatus = getTemporaryCredentials( &transportInterface, pDateISO8601, sizeof( pDateISO8601 ), &credentialResponse, &sigvCreds );

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

        /******************** Print S3 Object Presigned URL. **********************/

        pPath = AWS_S3_URI_PATH;

        if( returnStatus == EXIT_SUCCESS )
        {
            ret = printS3ObjectFilePresignedURL( serverHost,
                                                 serverHostLength,
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
