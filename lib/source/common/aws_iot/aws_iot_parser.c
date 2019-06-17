/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_parser.c
 * @brief Parses topics for Thing Name and status.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* AWS IoT include. */
#include "private/aws_iot.h"

/* Error handling include. */
#include "private/iot_error.h"

/*-----------------------------------------------------------*/

AwsIotStatus_t AwsIot_ParseStatus( const char * pTopicName,
                                   uint16_t topicNameLength )
{
    IOT_FUNCTION_ENTRY( AwsIotStatus_t, AWS_IOT_UNKNOWN );
    const char * pSuffixStart = NULL;

    /* Check that the status topic name is at least as long as the
     * "accepted" suffix. */
    if( topicNameLength > AWS_IOT_ACCEPTED_SUFFIX_LENGTH )
    {
        /* Calculate where the "accepted" suffix should start. */
        pSuffixStart = pTopicName + topicNameLength - AWS_IOT_ACCEPTED_SUFFIX_LENGTH;

        /* Check if the end of the status topic name is "/accepted". */
        if( strncmp( pSuffixStart,
                     AWS_IOT_ACCEPTED_SUFFIX,
                     AWS_IOT_ACCEPTED_SUFFIX_LENGTH ) == 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_ACCEPTED );
        }
    }

    /* Check that the status topic name is at least as long as the
     * "rejected" suffix. */
    if( topicNameLength > AWS_IOT_REJECTED_SUFFIX_LENGTH )
    {
        /* Calculate where the "rejected" suffix should start. */
        pSuffixStart = pTopicName + topicNameLength - AWS_IOT_REJECTED_SUFFIX_LENGTH;

        /* Check if the end of the status topic name is "/rejected". */
        if( strncmp( pSuffixStart,
                     AWS_IOT_REJECTED_SUFFIX,
                     AWS_IOT_REJECTED_SUFFIX_LENGTH ) == 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_REJECTED );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/
