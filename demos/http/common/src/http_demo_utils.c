/*
 * AWS IoT Device SDK for Embedded C V202011.00
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

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

#include "http_demo_utils.h"

/* Retry utilities. */
#include "retry_utils.h"

/* Third party parser utilities. */
#include "http_parser.h"

/*-----------------------------------------------------------*/

int32_t connectToServerWithBackoffRetries( TransportConnect_t connectFunction,
                                           NetworkContext_t * pNetworkContext )
{
    int32_t returnStatus = EXIT_FAILURE;
    /* Status returned by the retry utilities. */
    RetryUtilsStatus_t retryUtilsStatus = RetryUtilsSuccess;
    /* Struct containing the next backoff time. */
    RetryUtilsParams_t reconnectParams;

    assert( connectFunction != NULL );

    /* Initialize reconnect attempts and interval */
    RetryUtils_ParamsReset( &reconnectParams );

    /* Attempt to connect to HTTP server. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached. */
    do
    {
        returnStatus = connectFunction( pNetworkContext );

        if( returnStatus != EXIT_SUCCESS )
        {
            LogWarn( ( "Connection to the HTTP server failed. "
                       "Retrying connection with backoff and jitter." ) );
            retryUtilsStatus = RetryUtils_BackoffAndSleep( &reconnectParams );
        }
    } while( ( returnStatus == EXIT_FAILURE ) && ( retryUtilsStatus == RetryUtilsSuccess ) );

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
