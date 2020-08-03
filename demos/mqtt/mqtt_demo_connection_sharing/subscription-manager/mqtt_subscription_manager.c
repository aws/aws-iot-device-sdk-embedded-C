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
 * @file mqtt_subscription_manager.c
 * @brief Implementation of the API of a subscription manager for handling subscription callbacks
 * to topic filters in MQTT operations.
 */

/* Standard includes. */
#include <string.h>
#include <assert.h>

/* Include demo config file. */
#include "demo_config.h"

/* Include header for the subscription manager. */
#include "mqtt_subscription_manager.h"

/**
 * @brief Represents a registered record of the topic filter and its associated callback
 * in the subscription manager registry.
 */
typedef struct SubscriptionManager_Record
{
    const char * pTopicFilter;
    uint16_t topicFilterLength;
    SubscriptionManager_Callback_t callback;
} SubscriptionManager_Record_t;

/**
 * @brief The default value for the maximum size of the callback registry in the
 * subscription manager.
 */
#ifndef MAX_SUBSCRIPTION_CALLBACK_RECORDS
    #define MAX_SUBSCRIPTION_CALLBACK_RECORDS    5
#endif

/**
 * @brief The registry to store records of topic filters and their subscription callbacks.
 */
static SubscriptionManager_Record_t callbackRecordList[ MAX_SUBSCRIPTION_CALLBACK_RECORDS ] = { 0 };

/**
 * @brief Handle special corner cases regarding wildcards at the end of topic
 * filters, as documented by the MQTT protocol spec.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] topicFilterLength Length of the topic filter being examined.
 * @param[in] topicNameLength Length of the topic name being examined.
 * @param[in] nameIndex Index of the topic name being examined.
 * @param[in] filterIndex Index of the topic filter being examined.
 * @param[out] pMatch Whether the topic filter and topic name match.
 *
 * @return `true` if the caller of this function should exit; `false` if the caller
 * should continue parsing the topics.
 */
static bool matchEndWildcards( const char * pTopicFilter,
                               uint16_t topicFilterLength,
                               uint16_t topicNameLength,
                               uint16_t nameIndex,
                               uint16_t filterIndex,
                               bool * pMatch );

/**
 * @brief Attempt to match characters in a topic filter by wildcards.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] filterIndex Index of the wildcard in the topic filter.
 * @param[in,out] pNameIndex Index of character in topic name. This variable is
 * advanced for `+` wildcards.
 * @param[out] pMatch Whether the topic filter and topic name match.
 *
 * @return `true` if the caller of this function should exit; `false` if the caller
 * should continue parsing the topics.
 */
static bool matchWildcards( const char * pTopicFilter,
                            const char * pTopicName,
                            uint16_t topicNameLength,
                            uint16_t filterIndex,
                            uint16_t * pNameIndex,
                            bool * pMatch );

/**
 * @brief Match a topic name and topic filter allowing the use of wildcards.
 *
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of topic filter.
 *
 * @return `true` if the topic name and topic filter match; `false` otherwise.
 */
static bool topicFilterMatch( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength );

/**
 * @brief Matches a topic name (from a incoming PUBLISH) with a topic filter.
 *
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of topic filter.
 *
 * @return `true` if the topic name and topic filter match; `false`
 * otherwise.
 */
static bool matchTopic( const char * pTopicName,
                        const uint16_t topicNameLength,
                        const char * pTopicFilter,
                        const uint16_t topicFilterLength );

/*-----------------------------------------------------------*/

static bool matchEndWildcards( const char * pTopicFilter,
                               uint16_t topicFilterLength,
                               uint16_t topicNameLength,
                               uint16_t nameIndex,
                               uint16_t filterIndex,
                               bool * pMatch )
{
    bool status = false, endChar = false;

    /* Determine if the last character is reached for both topic name and topic
     * filter for the '#' wildcard. */
    endChar = ( nameIndex == ( topicNameLength - 1U ) ) && ( filterIndex == ( topicFilterLength - 3U ) );

    if( endChar == true )
    {
        /* Determine if the topic filter ends with the '#' wildcard. */
        status = ( pTopicFilter[ filterIndex + 2U ] == '#' );
    }

    if( status == false )
    {
        /* Determine if the last character is reached for both topic name and topic
         * filter for the '+' wildcard. */
        endChar = ( nameIndex == ( topicNameLength - 1U ) ) && ( filterIndex == ( topicFilterLength - 2U ) );

        if( endChar == true )
        {
            /* Filter "sport/+" also matches the "sport/" but not "sport". */
            status = ( pTopicFilter[ filterIndex + 1U ] == '+' );
        }
    }

    *pMatch = status;

    return status;
}

/*-----------------------------------------------------------*/

static bool matchWildcards( const char * pTopicFilter,
                            const char * pTopicName,
                            uint16_t topicNameLength,
                            uint16_t filterIndex,
                            uint16_t * pNameIndex,
                            bool * pMatch )
{
    bool status = false;

    /* Check for wildcards. */
    if( pTopicFilter[ filterIndex ] == '+' )
    {
        /* Move topic name index to the end of the current level.
         * This is identified by '/'. */
        while( ( *pNameIndex < topicNameLength ) && ( pTopicName[ *pNameIndex ] != '/' ) )
        {
            ( *pNameIndex )++;
        }

        ( *pNameIndex )--;
    }
    else if( pTopicFilter[ filterIndex ] == '#' )
    {
        /* Subsequent characters don't need to be checked for the
         * multi-level wildcard. */
        *pMatch = true;
        status = true;
    }
    else
    {
        /* Any character mismatch other than '+' or '#' means the topic
         * name does not match the topic filter. */
        *pMatch = false;
        status = true;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool topicFilterMatch( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength )
{
    bool status = false, matchFound = false;
    uint16_t nameIndex = 0, filterIndex = 0;

    assert( pTopicName != NULL );
    assert( topicNameLength != 0 );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );

    while( ( nameIndex < topicNameLength ) && ( filterIndex < topicFilterLength ) )
    {
        /* Check if the character in the topic name matches the corresponding
         * character in the topic filter string. */
        if( pTopicName[ nameIndex ] == pTopicFilter[ filterIndex ] )
        {
            /* Handle special corner cases regarding wildcards at the end of
             * topic filters, as documented by the MQTT protocol spec. */
            matchFound = matchEndWildcards( pTopicFilter,
                                            topicFilterLength,
                                            topicNameLength,
                                            nameIndex,
                                            filterIndex,
                                            &status );
        }
        else
        {
            /* Check for matching wildcards. */
            matchFound = matchWildcards( pTopicFilter,
                                         pTopicName,
                                         topicNameLength,
                                         filterIndex,
                                         &nameIndex,
                                         &status );
        }

        if( matchFound == true )
        {
            break;
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    if( status == false )
    {
        /* If the end of both strings has been reached, they match. */
        status = ( ( nameIndex == topicNameLength ) && ( filterIndex == topicFilterLength ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool matchTopic( const char * pTopicName,
                        const uint16_t topicNameLength,
                        const char * pTopicFilter,
                        const uint16_t topicFilterLength )
{
    assert( pTopicName != NULL );
    assert( topicNameLength != 0 );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );

    bool status = false;

    /* Check for an exact match if the incoming topic name and the registered
     * topic filter length match. */
    if( topicNameLength == topicFilterLength )
    {
        status = ( strncmp( pTopicName, pTopicFilter, topicNameLength ) == 0 );
    }

    /* Match against wildcard characters in topic filter only if the incoming
     * PUBLISH topic name does not start with a "$" character. */
    else if( pTopicName[ 0 ] != '$' )
    {
        status = topicFilterMatch( pTopicName, topicNameLength, pTopicFilter, topicFilterLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

/* Design -
 *   * Common handler can contain logic of processing acks and retries.
 *   * Only forward PUBLISH message to message dispatcher/handler as individual callbacks
 *     only want to process incoming PUBLISH message.
 */
void SubscriptionManager_DispatchHandler( MQTTContext_t * pContext,
                                          MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    size_t listIndex = 0u;

    /* Iterate through record list to find matching topics, and invoke their callbacks. */
    while( listIndex < MAX_SUBSCRIPTION_CALLBACK_RECORDS )
    {
        if( matchTopic( pPublishInfo->pTopicName,
                        pPublishInfo->topicNameLength,
                        callbackRecordList[ listIndex ].pTopicFilter,
                        callbackRecordList[ listIndex ].topicFilterLength ) == true )
        {
            /* Invoke the callback associated with the record as the topics match. */
            callbackRecordList[ listIndex ].callback( pContext, pPublishInfo );
        }

        listIndex++;
    }
}

/*-----------------------------------------------------------*/

bool SubscriptionManager_RegisterCallback( const char * pTopicFilter,
                                           uint16_t topicFilterLength,
                                           SubscriptionManager_Callback_t callback )
{
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );

    bool recordAdded = false;
    size_t availableIndex = 0u;
    bool recordExists = false;

    /* Search for an available spot in the list to store the record */
    while( ( availableIndex < MAX_SUBSCRIPTION_CALLBACK_RECORDS ) &&
           ( callbackRecordList[ availableIndex ].pTopicFilter != NULL ) )
    {
        /* Check if a record for the topic filter already exists in the registry. */
        if( ( callbackRecordList[ availableIndex ].topicFilterLength == topicFilterLength ) &&
            ( strncmp( pTopicFilter, callbackRecordList[ availableIndex ].pTopicFilter, topicFilterLength )
              == 0 ) )
        {
            recordExists = true;
        }

        availableIndex++;
    }

    if( ( availableIndex == MAX_SUBSCRIPTION_CALLBACK_RECORDS ) || ( recordExists == true ) )
    {
        /* Either the record list is full OR the record for the topic filter already exists. */
    }
    else
    {
        /* Should the topic string be copied? */
        callbackRecordList[ availableIndex ].pTopicFilter = pTopicFilter;
        callbackRecordList[ availableIndex ].topicFilterLength = topicFilterLength;
        callbackRecordList[ availableIndex ].callback = callback;

        recordAdded = true;
    }

    return recordAdded;
}

/*-----------------------------------------------------------*/

void SubscriptionManager_RemoveCallback( const char * pTopicFilter,
                                         uint16_t topicFilterLength )
{
    size_t matchingRecordIndex = 0u;
    bool recordFound = false;
    SubscriptionManager_Record_t * pRecord = NULL;

    /* Iterate through the records list to find the matching record. */
    do
    {
        pRecord = &callbackRecordList[ matchingRecordIndex ];

        if( ( topicFilterLength == pRecord->topicFilterLength ) &&
            ( strncmp( pTopicFilter, pRecord->pTopicFilter, topicFilterLength ) == 0 ) )
        {
            recordFound = true;
        }
    } while( ( ++matchingRecordIndex < MAX_SUBSCRIPTION_CALLBACK_RECORDS ) && ( recordFound == false ) );

    /* Delete the record by clearing the found entry in the records list. */
    if( recordFound == true )
    {
        pRecord->pTopicFilter = NULL;
        pRecord->topicFilterLength = 0u;
        pRecord->callback = NULL;
    }
}
