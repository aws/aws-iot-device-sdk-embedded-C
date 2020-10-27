
/*
 * AWS IoT Device SDK for Embedded C V202009.00
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

/* Third party parser utilities. */
#include "http_parser.h"

/*-----------------------------------------------------------*/

void getUrlPath( const char * pUrl,
                 size_t urlLen,
                 const char ** pPath,
                 size_t * pPathLen )
{
    /* http-parser status. Initialized to 0 to signify success. */
    int parserStatus = 0;
    struct http_parser_url urlParser;

    /* Sets all members in urlParser to 0. */
    http_parser_url_init( &urlParser );


        parserStatus = http_parser_parse_url( pUrl, urlLen, 0, &urlParser );

        if( parserStatus != 0 )
        {
            OTA_LOG_L1( "Error parsing the input URL %.*s. Error code: %d.", urlLen, pUrl, parserStatus );
        }
        else
        {


        *pPathLen = ( size_t ) ( urlParser.field_data[ UF_PATH ].len );

        if( *pPathLen == 0 )
        {
            *pPath = NULL;
        }
        else
        {
            *pPath = &pUrl[ urlParser.field_data[ UF_PATH ].off ];
        }
    }

}

/*-----------------------------------------------------------*/

void  getUrlAddress( const char * pUrl,
                     size_t urlLen,
                     const char ** pAddress,
                     size_t * pAddressLen )
{
    /* http-parser status. Initialized to 0 to signify success. */
    int parserStatus = 0;
    struct http_parser_url urlParser;

    /* Sets all members in urlParser to 0. */
    http_parser_url_init( &urlParser );

        parserStatus = http_parser_parse_url( pUrl, urlLen, 0, &urlParser );

        if( parserStatus != 0 )
        {
            OTA_LOG_L1( "Error parsing the input URL %.*s. Error code: %d.", urlLen, pUrl, parserStatus );
        }
    else{

        *pAddressLen = ( size_t ) ( urlParser.field_data[ UF_HOST ].len );

        if( *pAddressLen == 0 )
        {
            *pAddress = NULL;
        }
        else
        {
            *pAddress = &pUrl[ urlParser.field_data[ UF_HOST ].off ];
        }
    }
}