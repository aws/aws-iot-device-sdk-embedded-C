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

#include "jobs.h"

typedef enum
{
    true = 1, false = 0
} bool_;

/**
 * @brief Table of topic API strings in JobsTopic_t order
 */
static const char * const apiTopic[] =
{
    JOBS_API_JOBSCHANGED,
    JOBS_API_NEXTJOBCHANGED,
    JOBS_API_GETPENDING JOBS_API_SUCCESS,
    JOBS_API_GETPENDING JOBS_API_FAILURE,
    JOBS_API_STARTNEXT JOBS_API_SUCCESS,
    JOBS_API_STARTNEXT JOBS_API_FAILURE,
    JOBS_API_DESCRIBE JOBS_API_SUCCESS,
    JOBS_API_DESCRIBE JOBS_API_FAILURE,
    JOBS_API_UPDATE JOBS_API_SUCCESS,
    JOBS_API_UPDATE JOBS_API_FAILURE,
};

/**
 * @brief Table of topic API string lengths in JobsTopic_t order
 */
static const size_t apiTopicLength[] =
{
    JOBS_API_JOBSCHANGED_LENGTH,
    JOBS_API_NEXTJOBCHANGED_LENGTH,
    JOBS_API_GETPENDING_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_GETPENDING_LENGTH + JOBS_API_FAILURE_LENGTH,
    JOBS_API_STARTNEXT_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_STARTNEXT_LENGTH + JOBS_API_FAILURE_LENGTH,
    JOBS_API_DESCRIBE_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_DESCRIBE_LENGTH + JOBS_API_FAILURE_LENGTH,
    JOBS_API_UPDATE_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_UPDATE_LENGTH + JOBS_API_FAILURE_LENGTH,
};

/**
 * @brief A strncpy replacement based on lengths only
 *
 * @param[in] buffer  The buffer to be written.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] value  The characters to copy.
 * @param[in] valueLength  How many characters to copy.
 *
 * @return #JobsSuccess if the value was written to the buffer;
 * #JobsBufferTooSmall if the buffer cannot hold the entire value.
 *
 * @note There is no harm from calling this function when
 * start >= max.  This allows for sequential calls to
 * strnAppend() where only the final call's return value
 * is needed.
 */
static JobsStatus_t strnAppend( char * buffer,
                                size_t * start,
                                size_t max,
                                const char * value,
                                size_t valueLength )
{
    size_t i = *start, j;

    for( j = 0U; ( i < max ) && ( j < valueLength ); i++, j++ )
    {
        buffer[ i ] = value[ j ];
    }

    *start = i;

    return ( i < max ) ? JobsSuccess : JobsBufferTooSmall;
}

/**
 * @brief Populate the common leading portion of a topic string.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in,out] start  The index at which to begin.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 */
static void writePreamble( char * buffer,
                           size_t * start,
                           size_t length,
                           const char * thingName,
                           uint16_t thingNameLength )
{
    ( void ) strnAppend( buffer, start, length,
                         JOBS_API_PREFIX, JOBS_API_PREFIX_LENGTH );
    ( void ) strnAppend( buffer, start, length,
                         thingName, thingNameLength );
    ( void ) strnAppend( buffer, start, length,
                         JOBS_API_BRIDGE, JOBS_API_BRIDGE_LENGTH );
}

#define checkThingParams()                                 \
    ( ( thingName != NULL ) && ( thingNameLength > 0U ) && \
      ( thingNameLength <= JOBS_THINGNAME_MAX_LENGTH ) )

#define checkCommonParams()                    \
    ( ( buffer != NULL ) && ( length > 0U ) && \
      checkThingParams() && ( outLength != NULL ) )

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a subscription request.
 */
JobsStatus_t Jobs_GetTopic( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            JobsTopic_t api,
                            size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() &&
        ( api > JobsInvalidTopic ) && ( api < JobsMaxTopic ) )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        if( api >= JobsDescribeSuccess )
        {
            ( void ) strnAppend( buffer, &start, length,
                                 "+/", ( sizeof( "+/" ) - 1U ) );
        }

        ret = strnAppend( buffer, &start, length,
                          apiTopic[ api ], apiTopicLength[ api ] );

        if( start == length )
        {
            start--;
        }

        buffer[ start ] = '\0';
        *outLength = start;
    }

    return ret;
}

/**
 * @brief Compare the leading n bytes of two character sequences.
 *
 * @param[in] a  first character sequence
 * @param[in] b  second character sequence
 * @param[in] n  number of bytes
 *
 * @return JobsSuccess if the sequences are the same;
 * JobsNoMatch otherwise
 */
static JobsStatus_t strnEq( const char * a,
                            const char * b,
                            size_t n )
{
    size_t i;

    for( i = 0U; i < n; i++ )
    {
        if( a[ i ] != b[ i ] )
        {
            break;
        }
    }

    return ( i == n ) ? JobsSuccess : JobsNoMatch;
}

/**
 * @brief Wrap strnEq() with a check to compare two lengths.
 */
static JobsStatus_t strnnEq( const char * a,
                             size_t aLength,
                             const char * b,
                             size_t bLength )
{
    JobsStatus_t ret = JobsNoMatch;

    if( aLength == bLength )
    {
        ret = strnEq( a, b, aLength );
    }

    return ret;
}

/**
 * @brief predicate returns true for a valid job ID character
 */
static bool_ isJobIdChar( char a )
{
    bool_ ret;

    if( ( a == '-' ) || ( a == '_' ) )
    {
        ret = true;
    }
    else if( ( a >= '0' ) && ( a <= '9' ) )
    {
        ret = true;
    }
    else if( ( a >= 'A' ) && ( a <= 'Z' ) )
    {
        ret = true;
    }
    else if( ( a >= 'a' ) && ( a <= 'z' ) )
    {
        ret = true;
    }
    else
    {
        ret = false;
    }

    return ret;
}

/**
 * @brief predicate returns true for a valid job ID string
 */
static bool_ isValidJobId( const char * jobId,
                           uint16_t jobIdLength )
{
    bool_ ret = false;

    if( ( jobId != NULL ) && ( jobIdLength > 0U ) &&
        ( jobIdLength <= JOBS_JOBID_MAX_LENGTH ) )
    {
        size_t i;

        for( i = 0; i < jobIdLength; i++ )
        {
            if( isJobIdChar( jobId[ i ] ) == false )
            {
                break;
            }
        }

        ret = ( i == jobIdLength ) ? true : false;
    }

    return ret;
}

/**
 * @brief Search for the API portion of a topic string in a table
 *
 * @param[in] topic  The topic string to check.
 * @param[in] topicLength  The length of the topic string.
 * @param[out] outApi  The jobs topic API value if present, e.g., #JobsUpdateSuccess.
 * @param[out] outJobId  The beginning of the jobID in the topic string.
 * @param[out] outJobIdLength  The length of the jobID in the topic string.
 *
 * @return #JobsSuccess if a matching topic was found;
 * #JobsNoMatch if a matching topic was NOT found
 *   (parameter outApi gets #JobsInvalidTopic ).
 */
static JobsStatus_t matchApi( const char * topic,
                              size_t topicLength,
                              JobsTopic_t * outApi,
                              char ** outJobId,
                              uint16_t * outJobIdLength )
{
    JobsStatus_t ret = JobsNoMatch;
    char * p = ( char * ) topic;
    JobsTopic_t api;
    size_t length = topicLength;
    char * jobId = NULL;
    uint16_t jobIdLength = 0U;

    /* The first set of APIs do not have job IDs. */
    for( api = JobsJobsChanged; api < JobsDescribeSuccess; api++ )
    {
        ret = strnnEq( p, length, apiTopic[ api ], apiTopicLength[ api ] );

        if( ret == JobsSuccess )
        {
            *outApi = api;
            break;
        }
    }

    /* The remaining APIs must have a job ID. */
    if( ret == JobsNoMatch )
    {
        size_t i;

        for( i = 0U; i < length; i++ )
        {
            if( ( i > 0U ) && ( p[ i ] == '/' ) )
            {
                /* Save the leading job ID and its length. */
                jobId = p;
                jobIdLength = ( uint16_t ) i;

                /* Advance p to after the '/' and reduce buffer length
                 * for the remaining API search. */
                p = &p[ i + 1U ];
                length = length - i - 1U;
                break;
            }
            else if( isJobIdChar( p[ i ] ) == false )
            {
                break;
            }
            else
            {
            }
        }

        for( api = JobsDescribeSuccess; api < JobsMaxTopic; api++ )
        {
            ret = strnnEq( p, length, apiTopic[ api ], apiTopicLength[ api ] );

            if( ret == JobsSuccess )
            {
                *outApi = api;
                *outJobId = jobId;
                *outJobIdLength = jobIdLength;
                break;
            }
        }
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Output a topic value if a Jobs API topic string is present.
 */
JobsStatus_t Jobs_MatchTopic( const char * topic,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              JobsTopic_t * outApi,
                              char ** outJobId,
                              uint16_t * outJobIdLength )
{
    JobsStatus_t ret = JobsBadParameter;
    JobsTopic_t api = JobsInvalidTopic;
    char * jobId = NULL;
    uint16_t jobIdLength = 0U;

    if( ( topic != NULL ) && ( length > 0U ) && checkThingParams() &&
        ( outApi != NULL ) )
    {
        const char * prefix = topic;
        const char * name = &prefix[ JOBS_API_PREFIX_LENGTH ];
        const char * bridge = &name[ thingNameLength ];

        ret = JobsNoMatch;

        /* check the shortest match first */
        if( ( length > JOBS_API_COMMON_LENGTH( thingNameLength ) ) &&
            ( strnEq( bridge, JOBS_API_BRIDGE, JOBS_API_BRIDGE_LENGTH ) == JobsSuccess ) &&
            ( strnEq( prefix, JOBS_API_PREFIX, JOBS_API_PREFIX_LENGTH ) == JobsSuccess ) &&
            ( strnEq( name, thingName, thingNameLength ) == JobsSuccess ) )
        {
            const char * tail = &bridge[ JOBS_API_BRIDGE_LENGTH ];
            size_t tailLength = length - JOBS_API_COMMON_LENGTH( thingNameLength );

            ret = matchApi( tail, tailLength, &api, &jobId, &jobIdLength );
        }
    }

    if( outApi != NULL )
    {
        *outApi = api;
    }

    if( outJobId != NULL )
    {
        *outJobId = jobId;
    }

    if( outJobIdLength != NULL )
    {
        *outJobIdLength = jobIdLength;
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a GetPendingJobExecutions request.
 */
JobsStatus_t Jobs_GetPending( char * buffer,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ret = strnAppend( buffer, &start, length,
                          JOBS_API_GETPENDING, JOBS_API_GETPENDING_LENGTH );

        if( start == length )
        {
            start--;
        }

        buffer[ start ] = '\0';
        *outLength = start;
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a StartNextPendingJobExecution request.
 */
JobsStatus_t Jobs_StartNext( char * buffer,
                             size_t length,
                             const char * thingName,
                             uint16_t thingNameLength,
                             size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ret = strnAppend( buffer, &start, length,
                          JOBS_API_STARTNEXT, JOBS_API_STARTNEXT_LENGTH );

        if( start == length )
        {
            start--;
        }

        buffer[ start ] = '\0';
        *outLength = start;
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a DescribeJobExecution request.
 */
JobsStatus_t Jobs_Describe( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            const char * jobId,
                            uint16_t jobIdLength,
                            size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() &&
        ( isValidJobId( jobId, jobIdLength ) == true ) )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ( void ) strnAppend( buffer, &start, length,
                             jobId, jobIdLength );
        ( void ) strnAppend( buffer, &start, length,
                             "/", ( sizeof( "/" ) - 1U ) );
        ret = strnAppend( buffer, &start, length,
                          JOBS_API_DESCRIBE, JOBS_API_DESCRIBE_LENGTH );

        if( start == length )
        {
            start--;
        }

        buffer[ start ] = '\0';
        *outLength = start;
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for an UpdateJobExecution request.
 */
JobsStatus_t Jobs_Update( char * buffer,
                          size_t length,
                          const char * thingName,
                          uint16_t thingNameLength,
                          const char * jobId,
                          uint16_t jobIdLength,
                          size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() &&
        ( isValidJobId( jobId, jobIdLength ) == true ) )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ( void ) strnAppend( buffer, &start, length,
                             jobId, jobIdLength );
        ( void ) strnAppend( buffer, &start, length,
                             "/", ( sizeof( "/" ) - 1U ) );
        ret = strnAppend( buffer, &start, length,
                          JOBS_API_UPDATE, JOBS_API_UPDATE_LENGTH );

        if( start == length )
        {
            start--;
        }

        buffer[ start ] = '\0';
        *outLength = start;
    }

    return ret;
}
