/*
 * AWS IoT Device SDK for Embedded C 202103.00
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

/* Demo utils header. */
#include "http_demo_utils.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/*Include clock header for millisecond sleep function. */
#include "clock.h"

/* Third party parser utilities. */
#include "http_parser.h"

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/*-----------------------------------------------------------*/

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

#define HTTP_DEMO_RECEIVED_DATE_HEADER_FIELD       "date"

#define AWS_IOT_THING_NAME "MyHomeThermostat"

#define AWS_IOT_THING_NAME_HEADER_FIELD           "x-amz-iot-thing-name"

 #define AWS_IOT_CREDENTIAL_PROVIDER_FULL_ENDPOINT    "https://"    \
 AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT "/role-aliases/"    \
 AWS_IOT_CREDENTIAL_PROVIDER_ROLE "/credentials"

 #define AWS_IOT_CREDENTIAL_PROVIDER_ENDPOINT "c3tvrvalb8cjyy.credentials.iot.us-east-2.amazonaws.com"

/** 
 * @brief Role alias for accessing the credential provider. 
 */
#define AWS_IOT_CREDENTIAL_PROVIDER_ROLE "Thermostat-dynamodb-access-role-alias"

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct.
 * Because these utilities are shared by both plaintext and TLS demos,
 * we must define pParams as void *. */
struct NetworkContext
{
    void * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber();

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/

int32_t connectToServerWithBackoffRetries( TransportConnect_t connectFunction,
                                           NetworkContext_t * pNetworkContext )
{
    int32_t returnStatus = EXIT_FAILURE;
    /* Status returned by the retry utilities. */
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    /* Struct containing the next backoff time. */
    BackoffAlgorithmContext_t reconnectParams;
    uint16_t nextRetryBackOff = 0U;
    struct timespec tp;

    assert( connectFunction != NULL );

    /* Seed pseudo random number generator used in the demo for
     * backoff period calculation when retrying failed network operations
     * with broker. */

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );
    /* Seed pseudo random number generator with nanoseconds. */
    srand( tp.tv_nsec );

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &reconnectParams,
                                       CONNECTION_RETRY_BACKOFF_BASE_MS,
                                       CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       CONNECTION_RETRY_MAX_ATTEMPTS );

    /* Attempt to connect to HTTP server. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached. */
    do
    {
        returnStatus = connectFunction( pNetworkContext );

        if( returnStatus != EXIT_SUCCESS )
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &reconnectParams, generateRandomNumber(), &nextRetryBackOff );

            if( backoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the HTTP server failed. Retrying "
                           "connection after %hu ms backoff.",
                           ( unsigned short ) nextRetryBackOff ) );
                Clock_SleepMs( nextRetryBackOff );
            }
            else
            {
                LogError( ( "Connection to the HTTP server failed, all attempts exhausted." ) );
            }
        }
    } while( ( returnStatus == EXIT_FAILURE ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Connection to the server failed, all attempts exhausted." ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t getUrlPath( const char * pUrl,
                         size_t urlLen,
                         const char ** pPath,
                         size_t * pPathLen )
{
    /* http-parser status. Initialized to 1 to signify failure. */
    int parserStatus = 1;
    struct http_parser_url urlParser;
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* Sets all members in urlParser to 0. */
    http_parser_url_init( &urlParser );

    if( ( pUrl == NULL ) || ( pPath == NULL ) || ( pPathLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlPath()." ) );
        httpStatus = HTTPInvalidParameter;
    }

    if( httpStatus == HTTPSuccess )
    {
        parserStatus = http_parser_parse_url( pUrl, urlLen, 0, &urlParser );

        if( parserStatus != 0 )
        {
            LogError( ( "Error parsing the input URL %.*s. Error code: %d.",
                        ( int32_t ) urlLen,
                        pUrl,
                        parserStatus ) );
            httpStatus = HTTPParserInternalError;
        }
    }

    if( httpStatus == HTTPSuccess )
    {
        *pPathLen = ( size_t ) ( urlParser.field_data[ UF_PATH ].len );

        if( *pPathLen == 0 )
        {
            httpStatus = HTTPNoResponse;
            *pPath = NULL;
        }
        else
        {
            *pPath = &pUrl[ urlParser.field_data[ UF_PATH ].off ];
        }
    }

    if( httpStatus != HTTPSuccess )
    {
        LogError( ( "Error parsing the path from URL %s. Error code: %d",
                    pUrl,
                    httpStatus ) );
    }

    return httpStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t getUrlAddress( const char * pUrl,
                            size_t urlLen,
                            const char ** pAddress,
                            size_t * pAddressLen )


{
    /* http-parser status. Initialized to 1 to signify failure. */
    int parserStatus = 1;
    struct http_parser_url urlParser;
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* Sets all members in urlParser to 0. */
    http_parser_url_init( &urlParser );

    if( ( pUrl == NULL ) || ( pAddress == NULL ) || ( pAddressLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlAddress()." ) );
        httpStatus = HTTPInvalidParameter;
    }

    if( httpStatus == HTTPSuccess )
    {
        parserStatus = http_parser_parse_url( pUrl, urlLen, 0, &urlParser );

        if( parserStatus != 0 )
        {
            LogError( ( "Error parsing the input URL %.*s. Error code: %d.",
                        ( int32_t ) urlLen,
                        pUrl,
                        parserStatus ) );
            httpStatus = HTTPParserInternalError;
        }
    }

    if( httpStatus == HTTPSuccess )
    {
        *pAddressLen = ( size_t ) ( urlParser.field_data[ UF_HOST ].len );

        if( *pAddressLen == 0 )
        {
            httpStatus = HTTPNoResponse;
            *pAddress = NULL;
        }
        else
        {
            *pAddress = &pUrl[ urlParser.field_data[ UF_HOST ].off ];
        }
    }

    if( httpStatus != HTTPSuccess )
    {
        LogError( ( "Error parsing the address from URL %s. Error code %d",
                    pUrl,
                    httpStatus ) );
    }

    return httpStatus;
}

JSONStatus_t parseCredentials(HTTPResponse_t response ,SigV4Credentials_t*  sigvCreds)
{

        JSONStatus_t jsonStatus=JSONSuccess;

        jsonStatus=JSON_Search( response.pBody,
                    response.bodyLen,
                    "credentials.accessKeyId",
                    strlen("credentials.accessKeyId"),
                    (const char **)&(sigvCreds->pAccessKeyId ),
                    &(sigvCreds->accessKeyLen));

        if(jsonStatus != JSONSuccess){   
            LogError( ( "Error parsing accessKeyId in the credentials.") );
        }

        if(jsonStatus == JSONSuccess){      
            jsonStatus=JSON_Search( response.pBody,
                        response.bodyLen,
                        "credentials.secretAccessKey",
                        strlen("credentials.secretAccessKey"),
                        (const char **)&(sigvCreds->pSecretAccessKey),
                        &(sigvCreds->secretAccessKeyLen));
        }
        
        if(jsonStatus != JSONSuccess){   
            LogError( ( "Error parsing secretAccessKey in the credentials.") );
        }

        if(jsonStatus == JSONSuccess){    
            jsonStatus=JSON_Search( response.pBody,
                        response.bodyLen,
                        "credentials.sessionToken",
                        strlen("credentials.sessionToken"),
                        (const char **)&(sigvCreds->pSecurityToken),
                        &(sigvCreds->securityTokenLen));
        }

        if(jsonStatus != JSONSuccess){   
            LogError( ( "Error parsing sessionToken in the credentials.") );
        }
        
        if(jsonStatus == JSONSuccess){    
            jsonStatus=JSON_Search( response.pBody,
                        response.bodyLen,
                        "credentials.expiration",
                        strlen("credentials.expiration"),
                        (const char **)&(sigvCreds->pExpiration),
                        &(sigvCreds->expirationLen));
        }

        if(jsonStatus != JSONSuccess){   
            LogError( ( "Error parsing expiration date in the credentials.") );
        }
        
        return jsonStatus;
}

int getTemporaryCredentials(TransportInterface_t* transportInterface, char * pDateISO8601, size_t pDateISO8601Len, SigV4Credentials_t*  sigvCreds)
{

        /******************** Get Temporary Credentials. **********************/
        int returnStatus=EXIT_SUCCESS;
        HTTPRequestHeaders_t requestHeaders = { 0 };
        HTTPRequestInfo_t requestInfo = { 0 };
        HTTPResponse_t response = { 0 };
        uint8_t pAwsIotHttpBuffer[2048] = { 0 };
        uint8_t pS3HttpBuffer[2048] = { 0 };
        size_t pathLen = 0;
        size_t addressLen = 0;
        HTTPStatus_t httpStatus = HTTPSuccess;
        SigV4Status_t sigv4Status=SigV4Success;
        JSONStatus_t jsonStatus;
        const char * pAddress=NULL;
        const char *pDate;
        const char *pPath;
        size_t dateLen;

        /* Retrieve the address location and length from AWS_IOT_CREDENTIAL_PROVIDER_FULL_ENDPOINT. */
        httpStatus = getUrlAddress( AWS_IOT_CREDENTIAL_PROVIDER_FULL_ENDPOINT,
                                    sizeof(AWS_IOT_CREDENTIAL_PROVIDER_FULL_ENDPOINT)-1,
                                    &pAddress,
                                    &addressLen );
        returnStatus= (httpStatus == HTTPSuccess)? EXIT_SUCCESS:EXIT_FAILURE;

        if(returnStatus==EXIT_SUCCESS){
            httpStatus = getUrlPath( AWS_IOT_CREDENTIAL_PROVIDER_FULL_ENDPOINT,
                                        sizeof(AWS_IOT_CREDENTIAL_PROVIDER_FULL_ENDPOINT)-1,
                                            &pPath,
                                            &pathLen );
        }
        returnStatus= (httpStatus == HTTPSuccess)? EXIT_SUCCESS:EXIT_FAILURE;
        /* Request header buffer. */
        requestHeaders.pBuffer = pAwsIotHttpBuffer;
        requestHeaders.bufferLen = sizeof(pAwsIotHttpBuffer);


        /* Temporary token request. */
        requestInfo.pMethod = HTTP_METHOD_GET;
        requestInfo.methodLen = sizeof(HTTP_METHOD_GET)-1;
        requestInfo.pPath = pPath;
        requestInfo.pathLen = pathLen;
        requestInfo.pHost = pAddress;
        requestInfo.hostLen = addressLen;
        requestInfo.reqFlags=0;

        response.pBuffer = pAwsIotHttpBuffer;
        response.bufferLen= sizeof(pAwsIotHttpBuffer);
        response.pHeaderParsingCallback = NULL;

        if(returnStatus==EXIT_SUCCESS){
            httpStatus=HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
        }
        
        returnStatus= (httpStatus == HTTPSuccess)? EXIT_SUCCESS:EXIT_FAILURE;

        if(returnStatus==EXIT_SUCCESS){
        httpStatus=HTTPClient_AddHeader( &requestHeaders, 
                     AWS_IOT_THING_NAME_HEADER_FIELD, 
                     sizeof(AWS_IOT_THING_NAME_HEADER_FIELD)-1,
                     AWS_IOT_THING_NAME,
                     sizeof(AWS_IOT_THING_NAME));
        }
        returnStatus= (httpStatus == HTTPSuccess)? EXIT_SUCCESS:EXIT_FAILURE;

        if(returnStatus==EXIT_SUCCESS){
            httpStatus=HTTPClient_Send( transportInterface,
                    &requestHeaders,
                    NULL,
                    0,
                    &response,0 );
        }

        LogInfo( ( "HTTPSTATUS = %s", HTTPClient_strerror(httpStatus) ) );
        LogInfo( ( "HTTPSTATUS = %d", response.statusCode ) );
        LogInfo( ( "HTTPSTATUS = %s", response.pHeaders ) ); 

        returnStatus= (httpStatus == HTTPSuccess)? EXIT_SUCCESS:EXIT_FAILURE;

        if(returnStatus==EXIT_SUCCESS){
            jsonStatus=parseCredentials(response ,sigvCreds);
        }

        returnStatus= (jsonStatus == JSONSuccess)? EXIT_SUCCESS:EXIT_FAILURE;

        /* Get the current time from the http response. */
        if(returnStatus==EXIT_SUCCESS){
            httpStatus=HTTPClient_ReadHeader( &response, 
                                HTTP_DEMO_RECEIVED_DATE_HEADER_FIELD, 
                                sizeof(HTTP_DEMO_RECEIVED_DATE_HEADER_FIELD)-1, 
                                (const char **)&pDate,
                                &dateLen );
        }
        

        LogInfo( ( "JSONSTATUS = %d", jsonStatus ) );  

        returnStatus= (httpStatus == HTTPSuccess)? EXIT_SUCCESS:EXIT_FAILURE;

        if(returnStatus==EXIT_SUCCESS){
            sigv4Status=SigV4_AwsIotDateToIso8601( pDate,dateLen, pDateISO8601 ,pDateISO8601Len);
        }

        returnStatus= (sigv4Status == SigV4Success)? EXIT_SUCCESS:EXIT_FAILURE;
        
        LogInfo( ( "SIGv4STATUS = %s", pDateISO8601 ) );
        
        return returnStatus;
}