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

/**
 * @file shadow_demo_main.c
 *
 * @brief Demo for showing how to use the Device Shadow library's API. This version
 * of Device Shadow API provide macros and helper functions for assembling MQTT topics
 * strings, and for determining whether an incoming MQTT message is related to a
 * device shadow. The shadow can be either the classic shadow or a named shadow. Change
 * #SHADOW_NAME to select the shadow. The Device Shadow library does not depend on a MQTT library,
 * therefore the code for MQTT connections are placed in another file (shadow_demo_helpers.c)
 * to make it easy to read the code using Device Shadow library.
 *
 * This example assumes there is a powerOn state in the device shadow. It does the
 * following operations:
 * 1. Establish a MQTT connection by using the helper functions in shadow_demo_helpers.c.
 * 2. Assemble strings for the MQTT topics of device shadow, by using macros defined by the Device Shadow library.
 * 3. Subscribe to those MQTT topics by using helper functions in shadow_demo_helpers.c.
 * 4. Publish a desired state of powerOn by using helper functions in shadow_demo_helpers.c.  That will cause
 * a delta message to be sent to device.
 * 5. Handle incoming MQTT messages in eventCallback, determine whether the message is related to the device
 * shadow by using a function defined by the Device Shadow library (Shadow_MatchTopicString). If the message is a
 * device shadow delta message, set a flag for the main function to know, then the main function will publish
 * a second message to update the reported state of powerOn.
 * 6. Handle incoming message again in eventCallback. If the message is from update/accepted, verify that it
 * has the same clientToken as previously published in the update message. That will mark the end of the demo.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

/* Shadow config include. */
#include "shadow_config.h"

/* SHADOW API header. */
#include "shadow.h"

/* JSON API header. */
#include "core_json.h"

/* Clock for timer. */
#include "clock.h"

/* shadow demo helpers header. */
#include "shadow_demo_helpers.h"

/**
 * @brief The length of #THING_NAME.
 */
#define THING_NAME_LENGTH    ( ( uint16_t ) ( sizeof( THING_NAME ) - 1 ) )

/**
 * @brief Format string representing a Shadow document with a "desired" state.
 *
 * The real json document will look like this:
 * {
 *   "state": {
 *     "desired": {
 *       "powerOn": 1
 *     }
 *   },
 *   "clientToken": "021909"
 * }
 *
 * Note the client token, which is optional for all Shadow updates. The client
 * token must be unique at any given time, but may be reused once the update is
 * completed. For this demo, a timestamp is used for a client token.
 */
#define SHADOW_DESIRED_JSON     \
    "{"                         \
    "\"state\":{"               \
    "\"desired\":{"             \
    "\"powerOn\":%01d"          \
    "}"                         \
    "},"                        \
    "\"clientToken\":\"%06lu\"" \
    "}"

/**
 * @brief The expected size of #SHADOW_DESIRED_JSON.
 *
 * Because all the format specifiers in #SHADOW_DESIRED_JSON include a length,
 * its full actual size is known by pre-calculation, here's the formula why
 * the length need to minus 3:
 * 1. The length of "%01d" is 4.
 * 2. The length of %06lu is 5.
 * 3. The actual length we will use in case 1. is 1 ( for the state of powerOn ).
 * 4. The actual length we will use in case 2. is 6 ( for the clientToken length ).
 * 5. Thus the additional size 3 = 4 + 5 - 1 - 6 + 1 (termination character).
 *
 * In your own application, you could calculate the size of the json doc in this way.
 */
#define SHADOW_DESIRED_JSON_LENGTH    ( sizeof( SHADOW_DESIRED_JSON ) - 3 )

/**
 * @brief Format string representing a Shadow document with a "reported" state.
 *
 * The real json document will look like this:
 * {
 *   "state": {
 *     "reported": {
 *       "powerOn": 1
 *     }
 *   },
 *   "clientToken": "021909"
 * }
 *
 * Note the client token, which is required for all Shadow updates. The client
 * token must be unique at any given time, but may be reused once the update is
 * completed. For this demo, a timestamp is used for a client token.
 */
#define SHADOW_REPORTED_JSON    \
    "{"                         \
    "\"state\":{"               \
    "\"reported\":{"            \
    "\"powerOn\":%01d"          \
    "}"                         \
    "},"                        \
    "\"clientToken\":\"%06lu\"" \
    "}"

/**
 * @brief The expected size of #SHADOW_REPORTED_JSON.
 *
 * Because all the format specifiers in #SHADOW_REPORTED_JSON include a length,
 * its full size is known at compile-time by pre-calculation. Users could refer to
 * the way how to calculate the actual length in #SHADOW_DESIRED_JSON_LENGTH.
 */
#define SHADOW_REPORTED_JSON_LENGTH    ( sizeof( SHADOW_REPORTED_JSON ) - 3 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef SHADOW_MAX_DEMO_LOOP_COUNT
    #define SHADOW_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in seconds to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S           ( 5 )

/**
 * @brief JSON key for response code that indicates the type of error in
 * the error document received on topic `/delete/rejected`.
 */
#define SHADOW_DELETE_REJECTED_ERROR_CODE_KEY           "code"

/**
 * @brief Length of #SHADOW_DELETE_REJECTED_ERROR_CODE_KEY
 */
#define SHADOW_DELETE_REJECTED_ERROR_CODE_KEY_LENGTH    ( ( uint16_t ) ( sizeof( SHADOW_DELETE_REJECTED_ERROR_CODE_KEY ) - 1 ) )

/*-----------------------------------------------------------*/

/**
 * @brief The simulated device current power on state.
 */
static uint32_t currentPowerOnState = 0;

/**
 * @brief The flag to indicate the device current power on state changed.
 */
static bool stateChanged = false;

/**
 * @brief When we send an update to the device shadow, and if we care about
 * the response from cloud (accepted/rejected), remember the clientToken and
 * use it to match with the response.
 */
static uint32_t clientToken = 0U;

/**
 * @brief Indicator that an error occurred during the MQTT event callback. If an
 * error occurred during the MQTT event callback, then the demo has failed.
 */
static bool eventCallbackError = false;

/**
 * @brief Status of the response of Shadow delete operation from AWS IoT
 * message broker.
 */
static bool deleteResponseReceived = false;

/**
 * @brief Status of the Shadow delete operation.
 *
 * The Shadow delete status will be updated by the incoming publishes on the
 * MQTT topics for delete acknowledgement from AWS IoT message broker
 * (accepted/rejected). Shadow document is considered to be deleted if an
 * incoming publish is received on `/delete/accepted` topic or an incoming
 * publish is received on `/delete/rejected` topic with error code 404. Code 404
 * indicates that the Shadow document does not exist for the Thing yet.
 */
static bool shadowDeleted = false;

/*-----------------------------------------------------------*/

/**
 * @brief This example uses the MQTT library of the AWS IoT Device SDK for
 * Embedded C. This is the prototype of the callback function defined by
 * that library. It will be invoked whenever the MQTT library receives an
 * incoming message.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Process payload from /update/delta topic.
 *
 * This handler examines the version number and the powerOn state. If powerOn
 * state has changed, it sets a flag for the main function to take further actions.
 *
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void updateDeltaHandler( MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Process payload from /update/accepted topic.
 *
 * This handler examines the accepted message that carries the same clientToken
 * as sent before.
 *
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void updateAcceptedHandler( MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Process payload from `/delete/rejected` topic.
 *
 * This handler examines the rejected message to look for the reject reason code.
 * If the reject reason code is `404`, an attempt was made to delete a shadow
 * document which was not present yet. This is considered to be success for this
 * demo application.
 *
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void deleteRejectedHandler( MQTTPublishInfo_t * pPublishInfo );

/*-----------------------------------------------------------*/

static void deleteRejectedHandler( MQTTPublishInfo_t * pPublishInfo )
{
    JSONStatus_t result = JSONSuccess;
    char * pOutValue = NULL;
    uint32_t outValueLength = 0U;
    long errorCode = 0L;

    assert( pPublishInfo != NULL );
    assert( pPublishInfo->pPayload != NULL );

    LogInfo( ( "/delete/rejected json payload:%s.", ( const char * ) pPublishInfo->pPayload ) );

    /* The payload will look similar to this:
     * {
     *    "code": error-code,
     *    "message": "error-message",
     *    "timestamp": timestamp,
     *    "clientToken": "token"
     * }
     */

    /* Make sure the payload is a valid json document. */
    result = JSON_Validate( ( const char * ) pPublishInfo->pPayload,
                            pPublishInfo->payloadLength );

    if( result == JSONSuccess )
    {
        /* Then we start to get the version value by JSON keyword "version". */
        result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                              pPublishInfo->payloadLength,
                              SHADOW_DELETE_REJECTED_ERROR_CODE_KEY,
                              SHADOW_DELETE_REJECTED_ERROR_CODE_KEY_LENGTH,
                              &pOutValue,
                              ( size_t * ) &outValueLength );
    }
    else
    {
        LogError( ( "The json document is invalid!!" ) );
    }

    if( result == JSONSuccess )
    {
        LogInfo( ( "Error code is: %.*s.",
                   outValueLength,
                   pOutValue ) );

        /* Convert the extracted value to an unsigned integer value. */
        errorCode = strtoul( pOutValue, NULL, 10 );
    }
    else
    {
        LogError( ( "No error code in json document!!" ) );
    }

    LogInfo( ( "Error code:%ld.", errorCode ) );

    /* Mark Shadow delete operation as a success if error code is 404. */
    if( errorCode == 404UL )
    {
        shadowDeleted = true;
    }
}

/*-----------------------------------------------------------*/

static void updateDeltaHandler( MQTTPublishInfo_t * pPublishInfo )
{
    static uint32_t currentVersion = 0; /* Remember the latestVersion # we've ever received */
    uint32_t version = 0U;
    uint32_t newState = 0U;
    char * outValue = NULL;
    uint32_t outValueLength = 0U;
    JSONStatus_t result = JSONSuccess;

    assert( pPublishInfo != NULL );
    assert( pPublishInfo->pPayload != NULL );

    LogInfo( ( "/update/delta json payload:%s.", ( const char * ) pPublishInfo->pPayload ) );

    /* The payload will look similar to this:
     * {
     *      "version": 12,
     *      "timestamp": 1595437367,
     *      "state": {
     *          "powerOn": 1
     *      },
     *      "metadata": {
     *          "powerOn": {
     *          "timestamp": 1595437367
     *          }
     *      },
     *      "clientToken": "388062"
     *  }
     */

    /* Make sure the payload is a valid json document. */
    result = JSON_Validate( ( const char * ) pPublishInfo->pPayload,
                            pPublishInfo->payloadLength );

    if( result == JSONSuccess )
    {
        /* Then we start to get the version value by JSON keyword "version". */
        result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                              pPublishInfo->payloadLength,
                              "version",
                              sizeof( "version" ) - 1,
                              &outValue,
                              ( size_t * ) &outValueLength );
    }
    else
    {
        LogError( ( "The json document is invalid!!" ) );
        eventCallbackError = true;
    }

    if( result == JSONSuccess )
    {
        LogInfo( ( "version: %.*s",
                   outValueLength,
                   outValue ) );

        /* Convert the extracted value to an unsigned integer value. */
        version = ( uint32_t ) strtoul( outValue, NULL, 10 );
    }
    else
    {
        LogError( ( "No version in json document!!" ) );
        eventCallbackError = true;
    }

    LogInfo( ( "version:%d, currentVersion:%d \r\n", version, currentVersion ) );

    /* When the version is much newer than the on we retained, that means the powerOn
     * state is valid for us. */
    if( version > currentVersion )
    {
        /* Set to received version as the current version. */
        currentVersion = version;

        /* Get powerOn state from json documents. */
        result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                              pPublishInfo->payloadLength,
                              "state.powerOn",
                              sizeof( "state.powerOn" ) - 1,
                              &outValue,
                              ( size_t * ) &outValueLength );
    }
    else
    {
        /* In this demo, we discard the incoming message
         * if the version number is not newer than the latest
         * that we've received before. Your application may use a
         * different approach.
         */
        LogWarn( ( "The received version is smaller than current one!!" ) );
    }

    if( result == JSONSuccess )
    {
        /* Convert the powerOn state value to an unsigned integer value. */
        newState = ( uint32_t ) strtoul( outValue, NULL, 10 );

        LogInfo( ( "The new power on state newState:%d, currentPowerOnState:%d \r\n",
                   newState, currentPowerOnState ) );

        if( newState != currentPowerOnState )
        {
            /* The received powerOn state is different from the one we retained before, so we switch them
             * and set the flag. */
            currentPowerOnState = newState;

            /* State change will be handled in main(), where we will publish a "reported"
             * state to the device shadow. We do not do it here because we are inside of
             * a callback from the MQTT library, so that we don't re-enter
             * the MQTT library. */
            stateChanged = true;
        }
    }
    else
    {
        LogError( ( "No powerOn in json document!!" ) );
        eventCallbackError = true;
    }
}

/*-----------------------------------------------------------*/

static void updateAcceptedHandler( MQTTPublishInfo_t * pPublishInfo )
{
    char * outValue = NULL;
    uint32_t outValueLength = 0U;
    uint32_t receivedToken = 0U;
    JSONStatus_t result = JSONSuccess;

    assert( pPublishInfo != NULL );
    assert( pPublishInfo->pPayload != NULL );

    LogInfo( ( "/update/accepted json payload:%s.", ( const char * ) pPublishInfo->pPayload ) );

    /* Handle the reported state with state change in /update/accepted topic.
     * Thus we will retrieve the client token from the json document to see if
     * it's the same one we sent with reported state on the /update topic.
     * The payload will look similar to this:
     *  {
     *      "state": {
     *          "reported": {
     *          "powerOn": 1
     *          }
     *      },
     *      "metadata": {
     *          "reported": {
     *          "powerOn": {
     *              "timestamp": 1596573647
     *          }
     *          }
     *      },
     *      "version": 14698,
     *      "timestamp": 1596573647,
     *      "clientToken": "022485"
     *  }
     */

    /* Make sure the payload is a valid json document. */
    result = JSON_Validate( ( const char * ) pPublishInfo->pPayload,
                            pPublishInfo->payloadLength );

    if( result == JSONSuccess )
    {
        /* Get clientToken from json documents. */
        result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                              pPublishInfo->payloadLength,
                              "clientToken",
                              sizeof( "clientToken" ) - 1,
                              &outValue,
                              ( size_t * ) &outValueLength );
    }
    else
    {
        LogError( ( "Invalid json documents !!" ) );
        eventCallbackError = true;
    }

    if( result == JSONSuccess )
    {
        LogInfo( ( "clientToken: %.*s", outValueLength,
                   outValue ) );

        /* Convert the code to an unsigned integer value. */
        receivedToken = ( uint32_t ) strtoul( outValue, NULL, 10 );

        LogInfo( ( "receivedToken:%d, clientToken:%u \r\n", receivedToken, clientToken ) );

        /* If the clientToken in this update/accepted message matches the one we
         * published before, it means the device shadow has accepted our latest
         * reported state. We are done. */
        if( receivedToken == clientToken )
        {
            LogInfo( ( "Received response from the device shadow. Previously published "
                       "update with clientToken=%u has been accepted. ", clientToken ) );
        }
        else
        {
            LogWarn( ( "The received clientToken=%u is not identical with the one=%u we sent "
                       , receivedToken, clientToken ) );
        }
    }
    else
    {
        LogError( ( "No clientToken in json document!!" ) );
        eventCallbackError = true;
    }
}

/*-----------------------------------------------------------*/

/* This is the callback function invoked by the MQTT stack when it receives
 * incoming messages. This function demonstrates how to use the Shadow_MatchTopicString
 * function to determine whether the incoming message is a device shadow message
 * or not. If it is, it handles the message depending on the message type.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo )
{
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint8_t thingNameLength = 0U;
    const char * pShadowName = NULL;
    uint8_t shadowNameLength = 0U;
    uint16_t packetIdentifier;

    ( void ) pMqttContext;

    assert( pDeserializedInfo != NULL );
    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );

    packetIdentifier = pDeserializedInfo->packetIdentifier;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pDeserializedInfo->pPublishInfo != NULL );
        LogInfo( ( "pPublishInfo->pTopicName:%s.", pDeserializedInfo->pPublishInfo->pTopicName ) );

        /* Let the Device Shadow library tell us whether this is a device shadow message. */
        if( SHADOW_SUCCESS == Shadow_MatchTopicString( pDeserializedInfo->pPublishInfo->pTopicName,
                                                       pDeserializedInfo->pPublishInfo->topicNameLength,
                                                       &messageType,
                                                       &pThingName,
                                                       &thingNameLength,
                                                       &pShadowName,
                                                       &shadowNameLength ) )
        {
            /* Upon successful return, the messageType has been filled in. */
            if( messageType == ShadowMessageTypeUpdateDelta )
            {
                /* Handler function to process payload. */
                updateDeltaHandler( pDeserializedInfo->pPublishInfo );
            }
            else if( messageType == ShadowMessageTypeUpdateAccepted )
            {
                /* Handler function to process payload. */
                updateAcceptedHandler( pDeserializedInfo->pPublishInfo );
            }
            else if( messageType == ShadowMessageTypeUpdateDocuments )
            {
                LogInfo( ( "/update/documents json payload:%s.", ( const char * ) pDeserializedInfo->pPublishInfo->pPayload ) );
            }
            else if( messageType == ShadowMessageTypeUpdateRejected )
            {
                LogInfo( ( "/update/rejected json payload:%s.", ( const char * ) pDeserializedInfo->pPublishInfo->pPayload ) );
            }
            else if( messageType == ShadowMessageTypeDeleteAccepted )
            {
                LogInfo( ( "Received an MQTT incoming publish on /delete/accepted topic." ) );
                shadowDeleted = true;
                deleteResponseReceived = true;
            }
            else if( messageType == ShadowMessageTypeDeleteRejected )
            {
                /* Handler function to process payload. */
                deleteRejectedHandler( pDeserializedInfo->pPublishInfo );
                deleteResponseReceived = true;
            }
            else
            {
                LogInfo( ( "Other message type:%d !!", messageType ) );
            }
        }
        else
        {
            LogError( ( "Shadow_MatchTopicString parse failed:%s !!", ( const char * ) pDeserializedInfo->pPublishInfo->pTopicName ) );
            eventCallbackError = true;
        }
    }
    else
    {
        HandleOtherIncomingPacket( pPacketInfo, packetIdentifier );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of shadow demo.
 *
 * This main function demonstrates how to use the macros provided by the
 * Device Shadow library to assemble strings for the MQTT topics defined
 * by AWS IoT Device Shadow. Named shadow topic strings differ from unnamed
 * ("Classic") topic strings as indicated by the tokens within square brackets.
 *
 * The main function uses these macros for topics to subscribe to:
 * - SHADOW_TOPIC_STR_UPDATE_DELTA for "$aws/things/thingName/shadow[/name/shadowname]/update/delta"
 * - SHADOW_TOPIC_STR_UPDATE_ACC for "$aws/things/thingName/shadow[/name/shadowname]/update/accepted"
 * - SHADOW_TOPIC_STR_UPDATE_REJ for "$aws/things/thingName/shadow[/name/shadowname]/update/rejected"
 *
 * It also uses these macros for topics to publish to:
 * - SHADOW_TOPIC_STR_DELETE for "$aws/things/thingName/shadow[/name/shadowname]/delete"
 * - SHADOW_TOPIC_STR_UPDATE for "$aws/things/thingName/shadow[/name/shadowname]/update"
 *
 * The helper functions this demo uses for MQTT operations have internal
 * loops to process incoming messages. Those are not the focus of this demo
 * and therefore, are placed in a separate file shadow_demo_helpers.c.
 */
int main( int argc,
          char ** argv )
{
    int returnStatus = EXIT_SUCCESS;
    int demoRunCount = 0;

    /* A buffer containing the update document. It has static duration to prevent
     * it from being placed on the call stack. */
    static char updateDocument[ SHADOW_REPORTED_JSON_LENGTH + 1 ] = { 0 };

    ( void ) argc;
    ( void ) argv;

    do
    {
        returnStatus = EstablishMqttSession( eventCallback );

        if( returnStatus == EXIT_FAILURE )
        {
            /* Log error to indicate connection failure. */
            LogError( ( "Failed to connect to MQTT broker." ) );
        }
        else
        {
            /* Reset the shadow delete status flags. */
            deleteResponseReceived = false;
            shadowDeleted = false;

            /* First of all, try to delete any Shadow document in the cloud.
             * Try to subscribe to `/delete/accepted` and `/delete/rejected` topics. */
            returnStatus = SubscribeToTopic( SHADOW_TOPIC_STR_DELETE_ACC( THING_NAME, SHADOW_NAME ),
                                             SHADOW_TOPIC_LEN_DELETE_ACC( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );

            if( returnStatus == EXIT_SUCCESS )
            {
                /* Try to subscribe to `/delete/rejected` topic. */
                returnStatus = SubscribeToTopic( SHADOW_TOPIC_STR_DELETE_REJ( THING_NAME, SHADOW_NAME ),
                                                 SHADOW_TOPIC_LEN_DELETE_REJ( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                /* Publish to Shadow `delete` topic to attempt to delete the
                 * Shadow document if exists. */
                returnStatus = PublishToTopic( SHADOW_TOPIC_STR_DELETE( THING_NAME, SHADOW_NAME ),
                                               SHADOW_TOPIC_LEN_DELETE( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ),
                                               updateDocument,
                                               0U );
            }

            /* Unsubscribe from the `/delete/accepted` and 'delete/rejected` topics.*/
            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = UnsubscribeFromTopic( SHADOW_TOPIC_STR_DELETE_ACC( THING_NAME, SHADOW_NAME ),
                                                     SHADOW_TOPIC_LEN_DELETE_ACC( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = UnsubscribeFromTopic( SHADOW_TOPIC_STR_DELETE_REJ( THING_NAME, SHADOW_NAME ),
                                                     SHADOW_TOPIC_LEN_DELETE_REJ( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            /* Check if an incoming publish on `/delete/accepted` or `/delete/rejected`
             * topics. If a response is not received, mark the demo execution as a failure.*/
            if( ( returnStatus == EXIT_SUCCESS ) && ( deleteResponseReceived != true ) )
            {
                LogError( ( "Failed to receive a response for Shadow delete." ) );
                returnStatus = EXIT_FAILURE;
            }

            /* Check if Shadow document delete was successful. A delete can be
             * successful in cases listed below.
             *  1. If an incoming publish is received on `/delete/accepted` topic.
             *  2. If an incoming publish is received on `/delete/rejected` topic
             *     with an error code 404. This indicates that a delete was
             *     attempted when a Shadow document is not available for the
             *     Thing. */
            if( returnStatus == EXIT_SUCCESS )
            {
                if( shadowDeleted == false )
                {
                    LogError( ( "Shadow delete operation failed." ) );
                    returnStatus = EXIT_FAILURE;
                }
            }

            /* Successfully connect to MQTT broker, the next step is
             * to subscribe shadow topics. */
            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = SubscribeToTopic( SHADOW_TOPIC_STR_UPDATE_DELTA( THING_NAME, SHADOW_NAME ),
                                                 SHADOW_TOPIC_LEN_UPDATE_DELTA( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = SubscribeToTopic( SHADOW_TOPIC_STR_UPDATE_ACC( THING_NAME, SHADOW_NAME ),
                                                 SHADOW_TOPIC_LEN_UPDATE_ACC( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = SubscribeToTopic( SHADOW_TOPIC_STR_UPDATE_REJ( THING_NAME, SHADOW_NAME ),
                                                 SHADOW_TOPIC_LEN_UPDATE_REJ( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            /* This demo uses a constant #THING_NAME and #SHADOW_NAME known at compile time therefore
             * we can use macros to assemble shadow topic strings.
             * If the thing name or shadow name is only known at run time, then we could use the API
             * #Shadow_AssembleTopicString to assemble shadow topic strings, here is the example for /update/delta:
             *
             * For /update/delta:
             *
             * #define SHADOW_TOPIC_MAX_LENGTH  (256U)
             *
             * ShadowStatus_t shadowStatus = SHADOW_SUCCESS;
             * char topicBuffer[ SHADOW_TOPIC_MAX_LENGTH ] = { 0 };
             * uint16_t bufferSize = SHADOW_TOPIC_MAX_LENGTH;
             * uint16_t outLength = 0;
             * const char thingName[] = { "TestThingName" };
             * uint16_t thingNameLength  = ( sizeof( thingName ) - 1U );
             * const char shadowName[] = { "TestShadowName" };
             * uint16_t shadowNameLength  = ( sizeof( shadowName ) - 1U );
             *
             * shadowStatus = Shadow_AssembleTopicString( ShadowTopicStringTypeUpdateDelta,
             *                                            thingName,
             *                                            thingNameLength,
             *                                            shadowName,
             *                                            shadowNameLength,
             *                                            & ( topicBuffer[ 0 ] ),
             *                                            bufferSize,
             *                                            & outLength );
             */

            /* Then we publish a desired state to the /update topic. Since we've deleted
             * the device shadow at the beginning of the demo, this will cause a delta message
             * to be published, which we have subscribed to.
             * In many real applications, the desired state is not published by
             * the device itself. But for the purpose of making this demo self-contained,
             * we publish one here so that we can receive a delta message later.
             */
            if( returnStatus == EXIT_SUCCESS )
            {
                /* desired power on state . */
                LogInfo( ( "Send desired power state with 1." ) );

                ( void ) memset( updateDocument,
                                 0x00,
                                 sizeof( updateDocument ) );

                /* Keep the client token in global variable used to compare if
                 * the same token in /update/accepted. */
                clientToken = ( Clock_GetTimeMs() % 1000000 );

                snprintf( updateDocument,
                          SHADOW_DESIRED_JSON_LENGTH + 1,
                          SHADOW_DESIRED_JSON,
                          ( int ) 1,
                          ( long unsigned ) clientToken );

                returnStatus = PublishToTopic( SHADOW_TOPIC_STR_UPDATE( THING_NAME, SHADOW_NAME ),
                                               SHADOW_TOPIC_LEN_UPDATE( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ),
                                               updateDocument,
                                               ( SHADOW_DESIRED_JSON_LENGTH + 1 ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                /* Note that PublishToTopic already called MQTT_ProcessLoop,
                 * therefore responses may have been received and the eventCallback
                 * may have been called, which may have changed the stateChanged flag.
                 * Check if the state change flag has been modified or not. If it's modified,
                 * then we publish reported state to update topic.
                 */
                if( stateChanged == true )
                {
                    /* Report the latest power state back to device shadow. */
                    LogInfo( ( "Report to the state change: %d", currentPowerOnState ) );
                    ( void ) memset( updateDocument,
                                     0x00,
                                     sizeof( updateDocument ) );

                    /* Keep the client token in global variable used to compare if
                     * the same token in /update/accepted. */
                    clientToken = ( Clock_GetTimeMs() % 1000000 );

                    snprintf( updateDocument,
                              SHADOW_REPORTED_JSON_LENGTH + 1,
                              SHADOW_REPORTED_JSON,
                              ( int ) currentPowerOnState,
                              ( long unsigned ) clientToken );

                    returnStatus = PublishToTopic( SHADOW_TOPIC_STR_UPDATE( THING_NAME, SHADOW_NAME ),
                                                   SHADOW_TOPIC_LEN_UPDATE( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ),
                                                   updateDocument,
                                                   ( SHADOW_REPORTED_JSON_LENGTH + 1 ) );
                }
                else
                {
                    LogInfo( ( "No change from /update/delta, unsubscribe all shadow topics and disconnect from MQTT.\r\n" ) );
                }
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                LogInfo( ( "Start to unsubscribe shadow topics and disconnect from MQTT. \r\n" ) );
                returnStatus = UnsubscribeFromTopic( SHADOW_TOPIC_STR_UPDATE_DELTA( THING_NAME, SHADOW_NAME ),
                                                     SHADOW_TOPIC_LEN_UPDATE_DELTA( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = UnsubscribeFromTopic( SHADOW_TOPIC_STR_UPDATE_ACC( THING_NAME, SHADOW_NAME ),
                                                     SHADOW_TOPIC_LEN_UPDATE_ACC( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = UnsubscribeFromTopic( SHADOW_TOPIC_STR_UPDATE_REJ( THING_NAME, SHADOW_NAME ),
                                                     SHADOW_TOPIC_LEN_UPDATE_REJ( THING_NAME_LENGTH, SHADOW_NAME_LENGTH ) );
            }

            /* The MQTT session is always disconnected, even there were prior failures. */
            returnStatus = DisconnectMqttSession();
        }

        /* This demo performs only Device Shadow operations. If matching the Shadow
         * topic fails or there are failures in parsing the received JSON document,
         * then this demo was not successful. */
        if( eventCallbackError == true )
        {
            returnStatus = EXIT_FAILURE;
        }

        /* Increment the demo run count. */
        demoRunCount++;

        if( returnStatus == EXIT_SUCCESS )
        {
            LogInfo( ( "Demo iteration %d is successful.", demoRunCount ) );
        }
        /* Attempt to retry a failed iteration of demo for up to #SHADOW_MAX_DEMO_LOOP_COUNT times. */
        else if( demoRunCount < SHADOW_MAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %d failed. Retrying...", demoRunCount ) );
            sleep( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S );
        }
        /* Failed all #SHADOW_MAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", SHADOW_MAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( returnStatus != EXIT_SUCCESS );

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Log message indicating the demo completed successfully. */
        LogInfo( ( "Demo completed successfully." ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/
