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

/* Include header for the subscription manager. */
#include "mqtt_subscription_manager.h"

/**
 * @brief Represents a registered record of the topic filter and its associated callback
 * in the subscription manager registry.
 */
typedef struct SubscriptionManagerRecord
{
    const char * pTopicFilter;
    uint16_t topicFilterLength;
    SubscriptionManagerCallback_t callback;
} SubscriptionManagerRecord_t;

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
static SubscriptionManagerRecord_t callbackRecordList[ MAX_SUBSCRIPTION_CALLBACK_RECORDS ] = { 0 };

/**
 * @brief Handle special corner cases for wildcards at the end of topic
 * filters, as documented by the MQTT protocol spec.
 *
 * It concludes a match between the topic name and topic filter for the
 * following special cases:
 * - When the topic filter ends with '+' character, but the topic name only
 * ends with '/'.
 * - When the topic filter ends with "/#" characters, but the topic name
 * ends at the parent level.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] topicFilterLength Length of the topic filter being examined.
 * @param[in] topicNameLength Length of the topic name being examined.
 * @param[in] nameIndex Index of the topic name being examined.
 * @param[in] filterIndex Index of the topic filter being examined.
 *
 * @return Returns whether the topic filter and the topic name match.
 */
static bool matchWildcardsSpecialCases( const char * pTopicFilter,
                                        uint16_t topicFilterLength,
                                        uint16_t topicNameLength,
                                        uint16_t nameIndex,
                                        uint16_t filterIndex );

/**
 * @brief Attempt to match topic name with a topic filter starting with a wildcard.
 *
 * If the topic filter starts with a '+' (single-level) wildcard, the function
 * advances the @a pNameIndex by a level in the topic name.
 * If the topic filter starts with a '#' (multi-level) wildcard, the function
 * concludes that both the topic name and topic filter match.
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
static bool matchTopicFilter( const char * pTopicName,
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

static bool matchWildcardsSpecialCases( const char * pTopicFilter,
                                        uint16_t topicFilterLength,
                                        uint16_t topicNameLength,
                                        uint16_t nameIndex,
                                        uint16_t filterIndex )
{
    bool matchFound = false;

    /* Determine if the last character is reached for the topic name, and the
     * third to last character is reached for the topic filter. */
    if( ( nameIndex == ( topicNameLength - 1U ) ) &&
        ( filterIndex == ( topicFilterLength - 3U ) ) )
    {
        /* Determine if the topic filter contains "/#" as the last 2 characters.
         * The '#' wildcard represents the parent and any number of child levels
         * in the topic name. For example, the filter "sport/#" matches "sport"
         * as well as "sport/tennis" topics. */
        matchFound = ( ( pTopicFilter[ filterIndex + 1U ] == '/' ) &&
                       ( pTopicFilter[ filterIndex + 2U ] == '#' ) ) ? true : false;
    }
    else
    {
        /* Determine if the last character is reached for the topic name and,
         * the second to last character for the topic filter. */
        if( ( nameIndex == ( topicNameLength - 1U ) ) &&
            ( filterIndex == ( topicFilterLength - 2U ) ) )
        {
            /* Determine if the topic filter contains "+" as the last character.
             * This covers the special case of topic matching when the topic name
             * ends with '/' but the topic filter ends with "/+". Thus, for example,
             * topic filter "sport/+" matches the "sport/" but not "sport". */
            matchFound = ( pTopicFilter[ filterIndex + 1U ] == '+' ) ? true : false;
        }
    }

    return matchFound;
}

/*-----------------------------------------------------------*/

static bool matchWildcards( const char * pTopicFilter,
                            const char * pTopicName,
                            uint16_t topicNameLength,
                            uint16_t filterIndex,
                            uint16_t * pNameIndex,
                            bool * pMatch )
{
    bool shouldStopMatching = false;

    /* Check for wildcards. */
    if( pTopicFilter[ filterIndex ] == '+' )
    {
        /* Move topic name index to the end of the current level.
         * This is identified by '/'. */
        while( ( *pNameIndex < topicNameLength ) && ( pTopicName[ *pNameIndex ] != '/' ) )
        {
            ( *pNameIndex )++;
        }

        /* Decrement the topic name index for 2 different cases:
         * - If the break condition is ( *pNameIndex < topicNameLength ), then
         * we have reached the end of the topic name.
         * - If the break condition is ( pTopicName[ *pNameIndex ] != '/' ),
         * we move back the index on the '/' character to be at the last
         * position in the current topic level. */
        ( *pNameIndex )--;
    }
    else if( pTopicFilter[ filterIndex ] == '#' )
    {
        /* Subsequent characters don't need to be checked for the
         * multi-level wildcard. */
        *pMatch = true;
        shouldStopMatching = true;
    }
    else
    {
        /* Any character mismatch other than '+' or '#' means the topic
         * name does not match the topic filter. */
        *pMatch = false;
        shouldStopMatching = true;
    }

    return shouldStopMatching;
}

/*-----------------------------------------------------------*/

static bool matchTopicFilter( const char * pTopicName,
                              uint16_t topicNameLength,
                              const char * pTopicFilter,
                              uint16_t topicFilterLength )
{
    bool matchFound = false, shouldStopMatching = false;
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
            matchFound = matchWildcardsSpecialCases( pTopicFilter,
                                                     topicFilterLength,
                                                     topicNameLength,
                                                     nameIndex,
                                                     filterIndex );
        }
        else
        {
            /* Check for matching wildcards. */
            shouldStopMatching = matchWildcards( pTopicFilter,
                                                 pTopicName,
                                                 topicNameLength,
                                                 filterIndex,
                                                 &nameIndex,
                                                 &matchFound );
        }

        if( ( matchFound == true ) || ( shouldStopMatching == true ) )
        {
            break;
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    if( matchFound == false )
    {
        /* If the end of both strings has been reached, they match. This represents the
         * case when the topic filter contains the '+' wildcard at a non-starting position.
         * For example, when matching either of "sport/+/player" OR "sport/hockey/+" topic
         * filters with "sport/hockey/player" topic name. */
        matchFound = ( ( nameIndex == topicNameLength ) &&
                       ( filterIndex == topicFilterLength ) ) ? true : false;
    }

    return matchFound;
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
    bool topicFilterStartsWithWildcard = false;

    /* Check for an exact match if the incoming topic name and the registered
     * topic filter length match. */
    if( topicNameLength == topicFilterLength )
    {
        status = ( strncmp( pTopicName, pTopicFilter, topicNameLength ) == 0 ) ? true : false;
    }

    if( status == false )
    {
        /* If an exact match was not found, match against wildcard characters in
         * topic filter.*/

        /* Determine if topic filter starts with a wildcard. */
        topicFilterStartsWithWildcard = ( ( pTopicFilter[ 0 ] == '+' ) ||
                                          ( pTopicFilter[ 0 ] == '#' ) ) ? true : false;

        /* Note: According to the MQTT 3.1.1 specification, incoming PUBLISH topic names
         * starting the "$" character cannot be matched against topic filter starting with
         * a wildcard, i.e. for example, "$SYS/sport" cannot be matched with "#" or
         * "+/sport" topic filters. */
        if( !( ( pTopicName[ 0 ] == '$' ) && ( topicFilterStartsWithWildcard == true ) ) )
        {
            status = matchTopicFilter( pTopicName, topicNameLength, pTopicFilter, topicFilterLength );
        }
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
    for( listIndex = 0; listIndex < MAX_SUBSCRIPTION_CALLBACK_RECORDS; listIndex++ )
    {
        if( ( callbackRecordList[ listIndex ].pTopicFilter != NULL ) &&
            ( matchTopic( pPublishInfo->pTopicName,
                          pPublishInfo->topicNameLength,
                          callbackRecordList[ listIndex ].pTopicFilter,
                          callbackRecordList[ listIndex ].topicFilterLength ) == true ) )
        {
            LogInfo( ( "Invoking subscription callback of matching topic filter: "
                       "TopicFilter=%.*s, TopicName=%.*s",
                       callbackRecordList[ listIndex ].topicFilterLength,
                       callbackRecordList[ listIndex ].pTopicFilter,
                       pPublishInfo->topicNameLength,
                       pPublishInfo->pTopicName ) );

            /* Invoke the callback associated with the record as the topics match. */
            callbackRecordList[ listIndex ].callback( pContext, pPublishInfo );
        }
    }
}

/*-----------------------------------------------------------*/

SubscriptionManagerStatus_t SubscriptionManager_RegisterCallback( const char * pTopicFilter,
                                                                  uint16_t topicFilterLength,
                                                                  SubscriptionManagerCallback_t callback )
{
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );
    assert( callback != NULL );

    SubscriptionManagerStatus_t returnStatus;
    size_t availableIndex = MAX_SUBSCRIPTION_CALLBACK_RECORDS;
    bool recordExists = false;
    size_t index = 0u;

    /* Search for the first available spot in the list to store the record, and also check if
     * a record for the topic filter already exists. */
    while( ( recordExists == false ) && ( index < MAX_SUBSCRIPTION_CALLBACK_RECORDS ) )
    {
        /* Check if the index represents an empty spot in the registry. If we had already
         * found an empty spot in the list, we will not update it. */
        if( ( availableIndex == MAX_SUBSCRIPTION_CALLBACK_RECORDS ) &&
            ( callbackRecordList[ index ].pTopicFilter == NULL ) )
        {
            availableIndex = index;
        }

        /* Check if the current record's topic filter in the registry matches the topic filter
         * we are trying to register. */
        else if( ( callbackRecordList[ index ].topicFilterLength == topicFilterLength ) &&
                 ( strncmp( pTopicFilter, callbackRecordList[ index ].pTopicFilter, topicFilterLength )
                   == 0 ) )
        {
            recordExists = true;
        }

        index++;
    }

    if( recordExists == true )
    {
        /* The record for the topic filter already exists. */
        LogError( ( "Failed to register callback: Record for topic filter already exists: TopicFilter=%.*s",
                    topicFilterLength,
                    pTopicFilter ) );

        returnStatus = SUBSCRIPTION_MANAGER_RECORD_EXISTS;
    }
    else if( availableIndex == MAX_SUBSCRIPTION_CALLBACK_RECORDS )
    {
        /* The registry is full. */
        LogError( ( "Unable to register callback: Registry list is full: TopicFilter=%.*s, MaxRegistrySize=%u",
                    topicFilterLength,
                    pTopicFilter,
                    MAX_SUBSCRIPTION_CALLBACK_RECORDS ) );

        returnStatus = SUBSCRIPTION_MANAGER_REGISTRY_FULL;
    }
    else
    {
        callbackRecordList[ availableIndex ].pTopicFilter = pTopicFilter;
        callbackRecordList[ availableIndex ].topicFilterLength = topicFilterLength;
        callbackRecordList[ availableIndex ].callback = callback;

        returnStatus = SUBSCRIPTION_MANAGER_SUCCESS;

        LogDebug( ( "Added callback to registry: TopicFilter=%.*s",
                    topicFilterLength,
                    pTopicFilter ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

void SubscriptionManager_RemoveCallback( const char * pTopicFilter,
                                         uint16_t topicFilterLength )
{
    assert( pTopicFilter != NULL );
    assert( topicFilterLength != 0 );

    size_t index;
    SubscriptionManagerRecord_t * pRecord = NULL;

    /* Iterate through the records list to find the matching record. */
    for( index = 0; index < MAX_SUBSCRIPTION_CALLBACK_RECORDS; index++ )
    {
        pRecord = &callbackRecordList[ index ];

        /* Only match the non-empty records. */
        if( pRecord->pTopicFilter != NULL )
        {
            if( ( topicFilterLength == pRecord->topicFilterLength ) &&
                ( strncmp( pTopicFilter, pRecord->pTopicFilter, topicFilterLength ) == 0 ) )
            {
                break;
            }
        }
    }

    /* Delete the record by clearing the found entry in the records list. */
    if( index < MAX_SUBSCRIPTION_CALLBACK_RECORDS )
    {
        pRecord->pTopicFilter = NULL;
        pRecord->topicFilterLength = 0u;
        pRecord->callback = NULL;

        LogDebug( ( "Deleted callback record for topic filter: TopicFilter=%.*s",
                    topicFilterLength,
                    pTopicFilter ) );
    }
    else
    {
        LogWarn( ( "Attempted to remove callback for un-registered topic filter: TopicFilter=%.*s",
                   topicFilterLength,
                   pTopicFilter ) );
    }
}
/*-----------------------------------------------------------*/
