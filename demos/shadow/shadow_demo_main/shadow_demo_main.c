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
 * @file shadow_demo_main.c
 * @brief "Demo for showing how to use the Device Shadow library's API. This version
 * of Device Shadow API provide macros and helper functions for assembling MQTT topics
 * strings, and for determining whether an incoming MQTT message is related to the
 * device shadow. The Device Shadow library does not depend on a MQTT library,
 * therefore the code for MQTT connections are placed in another file (shadow_demo_helpers.c)
 * to make it easy to read the code using Device Shadow library.
 *
 * This example assumes there is a powerOn state in the device shadow. It does the
 * following operations:
 * 1. Establish a MQTT connection by using the helper functions in shadow_demo_helpers.c.
 * 2. Assemble strings for the MQTT topics of interest, by using macros defined by the Device Shadow library.
 * 3. Subscribe to those MQTT topics by using helper functions in shadow_demo_helpers.c.
 * 4. Publish a desire state of powerOn by using helper functions in shadow_demo_helpers.c.
 * 5. Handle incoming MQTT messages in eventCallback, determine whether the message is related to
 * the device shadow by using a function defined by the Device Shadow library (Shadow_MatchTopic).
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

#include "shadow_config.h"

/* SHADOW API header. */
#include "shadow.h"

/* JSON API header. */
#include "json.h"

/* shadow demo helpers header. */
#include "shadow_demo_helpers.h"


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
 * Note the client token, which is required for all Shadow updates. The client
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
 * its full size is known at compile-time. "In your own application, this might
 * not be true, then you should calculate the size of the json doc at run time.
 */
#define SHADOW_DESIRED_JSON_LENGTH    ( sizeof( SHADOW_DESIRED_JSON ) - 3 )

/**
 * @brief Format string representing a Shadow document with a "reported" state.
 *
 * The real json pay will look like this:
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
 * its full size is known at compile-time. "In your own application, this might
 * not be true, then you should calculate the size of the json doc at run time.
 */
#define SHADOW_REPORTED_JSON_LENGTH    ( sizeof( SHADOW_REPORTED_JSON ) - 3 )

/**
 * @brief Predefined thing name.
 *
 * This is the example predefine thing name and could be compiled in ROM code.
 */
#define THING_NAME                          "testShadow"

/**
 * @brief The length of #THING_NAME.
 */
#define THING_NAME_LENGTH                   ( ( uint16_t ) ( sizeof( THING_NAME ) - 1 ) )

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
 * use it to match with the response..
 */
static uint32_t clientToken = 0U;

/*-----------------------------------------------------------*/

/**
 * @brief This example uses the MQTT library of the AWS IoT Device SDK for
 * Embedded C. This is the prototype of the callback function defined by
 * that library. It will be invoked whenever the MQTT library receives an
 * incoming message..
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] packetIdentifier Packet identifier of the incoming packet.
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo );

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

/*-----------------------------------------------------------*/

static void updateDeltaHandler( MQTTPublishInfo_t * pPublishInfo )
{
    static uint32_t currentVersion = 0; /* Remember the latestVersion # we've ever received */
    uint32_t version = 0U;
    uint32_t newState = 0U;
    char * outValue = NULL;
    uint32_t outValueLength = 0U;

    assert( pPublishInfo != NULL );
    assert( pPublishInfo->pPayload != NULL );

    LogInfo( ( "/update/delta json payload:%s.\n\n", pPublishInfo->pPayload ) );
    /* Make sure the payload is json document. */
    if ( JSONSuccess == JSON_Validate( pPublishInfo->pPayload,
                                       pPublishInfo->payloadLength ) )
    {
        /* In this demo, we discard the incoming message
         * if the version number is not newer than the latest
         * that we've received before. Your application may use a
         * different approach. 
         */

        /* Then we start to get the version value by JSON keyword "version".
         * The payload will look similar to this:
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
        JSONStatus_t result = JSONSuccess;

        result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                              pPublishInfo->payloadLength,
                              "version",
                              sizeof("version") - 1,
                              '.',
                              & outValue,
                              ( size_t * ) & outValueLength );
        if ( result == JSONSuccess )
        {
            LogInfo( ( "version: %.*s\n\n",
                        outValueLength,
                        outValue ) );

            /* Convert the code to an unsigned integer value. */
            version = ( uint32_t ) strtoul( outValue, NULL, 10 );

            LogInfo( ( "version:%d, currentVersion:%d \r\n", version,  currentVersion) );

            if ( version > currentVersion )
            {
                /* Set to received version as the current version. */
                currentVersion = version;

                /* Get powerOn state from json documents. */
                result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                                      pPublishInfo->payloadLength,
                                      "state.powerOn",
                                      sizeof("state.powerOn") - 1,
                                      '.',
                                      & outValue,
                                      ( size_t * ) & outValueLength );

                if ( result == JSONSuccess )
                {
                    /* Convert the code to an unsigned integer value. */
                    newState = ( uint32_t ) strtoul( outValue, NULL, 10 );

                    LogInfo( ( "The new power on state newState:%d, currentPowerOnState:%d \r\n",
                               newState,  currentPowerOnState) );

                    if ( newState != currentPowerOnState )
                    {
                        currentPowerOnState = newState;

                        /* State change will be handled in main(), where we will publish a "reported"
                        * state to the device shadow. We do not do it here because we are inside of
                        * a callback from the MQTT library, so that we don't re-enter
                        * the MQTT library (even though the library might support re-entrance.) */
                        stateChanged = true;
                    }
                }
                else
                {
                    LogError( ( "No powerOn in json document!!\n\n" ) );
                }
            }
            else
            {
                LogError( ( "The received version is smaller than current one!!\n\n" ) );
            }
        }
        else
        {
            LogError( ( "No version in json document!!\n\n" ) );
        }
    }
    else
    {
        LogError( ( "The json document is invalid!!\n\n" ) );
    }
}

/*-----------------------------------------------------------*/

static void updateAcceptedHandler( MQTTPublishInfo_t * pPublishInfo )
{
    char * outValue = NULL;
    uint32_t outValueLength = 0U;
    uint32_t receivedToken = 0U;

    assert( pPublishInfo != NULL );
    assert( pPublishInfo->pPayload != NULL );

    LogInfo( ( "/update/accepted json payload:%s.\n\n", pPublishInfo->pPayload ) );

    /* Handle the reported state with state change in /update/accepted topic. */
    /* Thus we will retrieve the client token from the json document to see if
     * it's the same one we sent with reported state on the /update topic.
     */
    if ( JSONSuccess == JSON_Validate( pPublishInfo->pPayload,
                                       pPublishInfo->payloadLength ) )
    {
        /*
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

        JSONStatus_t result = JSONSuccess;

        /* Get clientToken from json documents. */
        result = JSON_Search( ( char * ) pPublishInfo->pPayload,
                              pPublishInfo->payloadLength,
                              "clientToken",
                              sizeof("clientToken") - 1,
                              '.',
                              & outValue,
                              ( size_t * ) & outValueLength );

        if ( result == JSONSuccess )
        {
            LogInfo( ( "clientToken: %.*s\n\n", outValueLength,
                                                outValue ) );

            /* Convert the code to an unsigned integer value. */
            receivedToken = ( uint32_t ) strtoul( outValue, NULL, 10 );

            LogInfo( ( "receivedToken:%d, clientToken:%u \r\n", receivedToken,  clientToken) );

            /* If the clientToken in this update/accepted message matches the one we
             * published before, it means the device shadow has accepted our latest
             * reported state. We are done. */
            if ( receivedToken == clientToken )
            {
                LogInfo( ( "Received response from the device shadow. Previously published "
                           "update with clientToken=%u has been accepted. \n\n", clientToken) );
            }
        }
        else
        {
            LogError( ( "No clientToken in json document!!\n\n" ) );
        }
    }
    else
    {
        LogError( ( "Invalid json documents !!\n\n" ) );
    }
}

/*-----------------------------------------------------------*/
/* This is the callback function invoked by the MQTT stack when it receives
 * incoming messages. This function demonstrates how to use the Shadow_MatchTopic
 * function to determine whether the incoming message is a device shadow message
 * or not. If it is, it handles the message depending on the message type.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           uint16_t packetIdentifier,
                           MQTTPublishInfo_t * pPublishInfo )
{
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint16_t thingNameLength = 0U;
    MQTTStatus_t mqttStatus = MQTTSuccess;

    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pPublishInfo != NULL );
        LogInfo( ( "pPublishInfo->pTopicName:%s.\n\n", pPublishInfo->pTopicName ) );

        /* Handle incoming publish. */
        /* Let the Device Shadow library tell us whether this is a device shadow message. */
        if( SHADOW_SUCCESS == Shadow_MatchTopic( pPublishInfo->pTopicName,
                                                        pPublishInfo->topicNameLength,
                                                        & messageType,
                                                        & pThingName,
                                                        & thingNameLength ) )
        {
            /* Upon successful return, the messageType has been filled in. */
            if( messageType == ShadowMessageTypeUpdateDelta )
            {
                /* Handler function to process payload. */
                updateDeltaHandler( pPublishInfo );
            }
            else if ( messageType == ShadowMessageTypeUpdateDocuments )
            {
                LogInfo( ( "/update/documents json payload:%s.\n\n", pPublishInfo->pPayload ) );
            }
            else if ( messageType == ShadowMessageTypeUpdateAccepted )
            {
                /* Handler function to process payload. */
                updateAcceptedHandler( pPublishInfo );
            }
            else if ( messageType == ShadowMessageTypeUpdateRejected )
            {
                LogInfo( ( "/update/rejected json payload:%s.\n\n", pPublishInfo->pPayload ) );
            }
            else
            {
                LogInfo( ( "Other message type:%d !!\n\n", messageType ) );
            }
        }
        else
        {
            LogError( ( "Shadow_MatchTopic parse failed:%s !!\n\n", pPublishInfo->pTopicName ) );
        }
    }
    else
    {
        handleOtherIncomingPacket( pPacketInfo, packetIdentifier );
    }
}

/*-----------------------------------------------------------*/
/**
 * @brief Entry point of shadow demo.
 *
 * This main function demonstrates how to use the macros provided by the
 * Device Shadow library to assemble strings for the MQTT topics defined
 * by AWS IoT Device Shadow. It uses these macros for topics to subscribe
 * to:
 * - SHADOW_TOPIC_STRING_UPDATE_DELTA for "$aws/things/thingName/shadow/update/delta"
 * - SHADOW_TOPIC_STRING_UPDATE_ACCEPTED for "$aws/things/thingName/shadow/update/accepted"
 * - SHADOW_TOPIC_STRING_UPDATE_REJECTED for "$aws/things/thingName/shadow/update/rejected"
 *
 * It also used these macros for topics to publish to:
 * - SHADOW_TOPIC_STIRNG_DELETE for "$aws/things/thingName/shadow/delete"
 * - SHADOW_TOPIC_STRING_UPDATE for "$aws/things/thingName/shadow/update"
 *
 * The helper functions this demo uses for MQTT operations have internal
 * loops process incoming messages. Those are not the focus of this demo
 * therefore placed in a separate file shadow_demo_helpers.c.
 */
int main( int argc,
          char ** argv )
{
    int returnStatus = EXIT_SUCCESS;
    /* A buffer containing the update document. It has static duration to prevent
    * it from being placed on the call stack. */
    static char updateDocument[ SHADOW_REPORTED_JSON_LENGTH + 1 ] = { 0 };
    int state = 1;

    ( void ) argc;
    ( void ) argv;

    returnStatus = establishMqttSession( eventCallback );

    if( returnStatus == EXIT_FAILURE )
    {
        /* Log error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to MQTT broker." ) );
    }
    else
    {
        /* First of all, try to delete any Shadow document in the cloud. */
        returnStatus = publishToTopic( SHADOW_TOPIC_STRING_DELETE( THING_NAME ),
                                       SHADOW_TOPIC_LENGTH_DELETE( THING_NAME_LENGTH ),
                                       updateDocument,
                                       0U );

        /* Successfully connect to MQTT broker, the next step is
         * to subscribe shadow topics. */
        if( returnStatus == EXIT_SUCCESS )
        {
            returnStatus = subscribeToTopic( SHADOW_TOPIC_STRING_UPDATE_DELTA( THING_NAME ),
                                             SHADOW_TOPIC_LENGTH_UPDATE_DELTA( THING_NAME_LENGTH ) );
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            returnStatus = subscribeToTopic( SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( THING_NAME ),
                                             SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( THING_NAME_LENGTH ) );
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            returnStatus = subscribeToTopic( SHADOW_TOPIC_STRING_UPDATE_REJECTED( THING_NAME ),
                                             SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( THING_NAME_LENGTH ) );
        }
        /* The shadow topics above could be decided at compile time because of known #THING_NAME in macro.
         * If the thing name is known at run time, then we could use the API #Shadow_GetTopicString to
         * generate shadow topics, here is the example for /update/delta:
         *
         * For /update/delta:
         *
         * #define SHADOW_TOPIC_MAX_LENGTH  (256U)
         *
         * ShadowStatus_t shadowStatus = SHADOW_STATUS_SUCCESS;
         * char topicBuffer[ SHADOW_TOPIC_MAX_LENGTH ] = { 0 };
         * uint16_t bufferSize = SHADOW_TOPIC_MAX_LENGTH;
         * uint16_t outLength = 0;
         *
         * shadowStatus = Shadow_GetTopicString( SHADOW_TOPIC_STRING_TYPE_UPDATE_DELTA,
         *                                       TEST_THING_NAME,
         *                                       TEST_THING_NAME_LENGTH,
         *                                       & ( topicBuffer[ 0 ] ),
         *                                       bufferSize,
         *                                       & outLength );
         * if ( shadowStatus == SHADOW_STATUS_SUCCESS )
         * {
         *      // You could get shadow topic at topicBuffer with length outLength.
         * }
         */

        /* Then we public desired state change to the shadow topic /update.
         * In many real applications, the desired state is not published by
         * the device itself. But for the purpose of making this demo self-contained,
         * we publish one here so that we can receive a delta message later.*/
        if( returnStatus == EXIT_SUCCESS )
        {
            /* desired power on state . */
            LogInfo( ( "Send desired power state with 1.\n\n" ) );

            ( void ) memset( updateDocument,
                             0x00,
                             sizeof( updateDocument ) );

            snprintf( updateDocument,
                      SHADOW_DESIRED_JSON_LENGTH + 1,
                      SHADOW_DESIRED_JSON,
                      ( int ) 1,
                      ( long unsigned ) ( Clock_GetTimeMs() % 1000000 ) );

            returnStatus = publishToTopic( SHADOW_TOPIC_STRING_UPDATE( THING_NAME ),
                                           SHADOW_TOPIC_LENGTH_UPDATE( THING_NAME_LENGTH ),
                                           updateDocument,
                                           ( SHADOW_DESIRED_JSON_LENGTH + 1 ) );
        }

        /* Check if the state change flag modified or not. If it's modified,
         * then we publish reported state to update topic.*/
        if( returnStatus == EXIT_SUCCESS )
        {
            /* Note that publishToTopic already called MQTT_ProcessLoop,
             * therefore responses may have been received and the eventCallback
             * may have been called, which may have changed the powerOn state. */
            if ( stateChanged == true )
            {
                /* Report the latest power state back to device shadow. */
                LogInfo( ( "Report to the state change: %d\n\n", currentPowerOnState ) );
                ( void ) memset( updateDocument,
                                 0x00,
                                 sizeof( updateDocument ) );
                /* keep the client token in global variable used to compare if
                   the same token in /update/accepted. */
                clientToken = ( Clock_GetTimeMs() % 1000000 );

                snprintf( updateDocument,
                          SHADOW_REPORTED_JSON_LENGTH + 1,
                          SHADOW_REPORTED_JSON,
                          ( int ) currentPowerOnState,
                          ( long unsigned ) clientToken );

                returnStatus= publishToTopic( SHADOW_TOPIC_STRING_UPDATE( THING_NAME ),
                                              SHADOW_TOPIC_LENGTH_UPDATE( THING_NAME_LENGTH ),
                                              updateDocument,
                                              ( SHADOW_DESIRED_JSON_LENGTH + 1 ) );
            }
            else
            {
                LogInfo( ( "No change from /update/delta, unsubscribe all shadow topics and disconnect from MQTT.\r\n") );
            }
        }

        LogInfo( ( "Start to unsubscribe shadow topics and disconnect from MQTT. \r\n") );
        unsubscribeFromTopic( SHADOW_TOPIC_STRING_UPDATE_DELTA( THING_NAME ),
                              SHADOW_TOPIC_LENGTH_UPDATE_DELTA( THING_NAME_LENGTH ) );

        unsubscribeFromTopic( SHADOW_TOPIC_STRING_UPDATE_ACCEPTED( THING_NAME ),
                              SHADOW_TOPIC_LENGTH_UPDATE_ACCEPTED( THING_NAME_LENGTH ) );

        unsubscribeFromTopic( SHADOW_TOPIC_STRING_UPDATE_REJECTED( THING_NAME ),
                              SHADOW_TOPIC_LENGTH_UPDATE_REJECTED( THING_NAME_LENGTH ) );

        disconnectMqttSession();
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/
