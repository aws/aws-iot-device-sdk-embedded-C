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
#include <stdlib.h>
#include <string.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Demo utils header. */
#include "http_demo_url_utils.h"

/*-----------------------------------------------------------*/

/**
 * @brief The separator between the "https" scheme and the host in a URL.
 */
#define SCHEME_SEPARATOR        "://"

/**
 * @brief The length of the "://" separator.
 */
#define SCHEME_SEPARATOR_LEN    ( sizeof( SCHEME_SEPARATOR ) - 1 )

/*-----------------------------------------------------------*/

HTTPStatus_t getUrlPath( const char * pUrl,
                         size_t urlLen,
                         const char ** pPath,
                         size_t * pPathLen )
{
    HTTPStatus_t httpStatus = HTTPSuccess;
    const char * pHostStart = NULL;
    const char * pPathStart = NULL;
    size_t hostLen = 0, i = 0, pathStartIndex = 0, pathLen = 0;

    if( ( pUrl == NULL ) || ( pPath == NULL ) || ( pPathLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlPath()." ) );
        httpStatus = HTTPInvalidParameter;
    }

    if( httpStatus == HTTPSuccess )
    {
        httpStatus = getUrlAddress( pUrl, urlLen, &pHostStart, &hostLen );
    }

    if( httpStatus == HTTPSuccess )
    {
        /* Search for the start of the path. */
        for( i = ( pHostStart - pUrl ) + hostLen; i < urlLen; i++ )
        {
            if( pUrl[ i ] == '/' )
            {
                pPathStart = &pUrl[ i ];
                pathStartIndex = i;
                break;
            }
        }

        if( pPathStart != NULL )
        {
            /* The end of the path will be either the start of the query,
             * start of the fragment, or end of the URL. If this is an S3
             * presigned URL, then there must be a query. */
            for( i = pathStartIndex; i < urlLen; i++ )
            {
                if( pUrl[ i ] == '?' )
                {
                    break;
                }
            }

            pathLen = i - pathStartIndex;
        }

        if( pathLen == 0 )
        {
            LogError( ( "Could not parse path from input URL %.*s",
                        ( int32_t ) urlLen,
                        pUrl ) );
            httpStatus = HTTPNoResponse;
        }
    }

    if( httpStatus == HTTPSuccess )
    {
        *pPathLen = pathLen;
        *pPath = pPathStart;
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
    HTTPStatus_t httpStatus = HTTPSuccess;
    const char * pHostStart = NULL;
    const char * pHostEnd = NULL;
    size_t i = 0, hostLen = 0;

    if( ( pUrl == NULL ) || ( pAddress == NULL ) || ( pAddressLen == NULL ) )
    {
        LogError( ( "NULL parameter passed to getUrlAddress()." ) );
        httpStatus = HTTPInvalidParameter;
    }

    if( httpStatus == HTTPSuccess )
    {
        /* Search for the start of the hostname using the "://" separator. */
        for( i = 0; i < ( urlLen - SCHEME_SEPARATOR_LEN ); i++ )
        {
            if( strncmp( &( pUrl[ i ] ), SCHEME_SEPARATOR, SCHEME_SEPARATOR_LEN ) == 0 )
            {
                pHostStart = pUrl + i + SCHEME_SEPARATOR_LEN;
                break;
            }
        }

        if( pHostStart == NULL )
        {
            LogError( ( "Could not find \"://\" scheme separator in input URL %.*s",
                        ( int32_t ) urlLen,
                        pUrl ) );
            httpStatus = HTTPParserInternalError;
        }
        else
        {
            /* Search for the end of the hostname assuming that the object path
             * is next. Assume that there is no port number as this is used for
             * S3 presigned URLs. */
            for( pHostEnd = pHostStart; pHostEnd < ( pUrl + urlLen ); pHostEnd++ )
            {
                if( *pHostEnd == '/' )
                {
                    hostLen = ( size_t ) ( pHostEnd - pHostStart );
                    break;
                }
            }
        }
    }

    if( httpStatus == HTTPSuccess )
    {
        *pAddressLen = hostLen;

        if( hostLen == 0 )
        {
            LogError( ( "Could not find end of host in input URL %.*s",
                        ( int32_t ) urlLen,
                        pUrl ) );
            httpStatus = HTTPNoResponse;
            *pAddress = NULL;
        }
        else
        {
            *pAddress = pHostStart;
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
