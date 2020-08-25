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
 * @file mqtt_config_defaults.h
 * @brief This represents the default values for the configuration macros
 * for the MQTT library.
 */

#ifndef MQTT_CONFIG_DEFAULTS_H_
#define MQTT_CONFIG_DEFAULTS_H_

/**
 * @brief Definition of logging macros to map logging calls within MQTT
 * library to application-specific logging implementation.
 *
 * Each logging macro represents a different logging level. Only define those
 * logging macros whose corresponding logging level messages are desired in
 * the MQTT library build.
 *
 * @note The logging macros are called in MQTT library with paramerers wrapped in
 * double parantheses to be ISO C89/C90 standard compliant. For an example
 * implementation of the logging macros, refer to mqtt_config.h files of MQTT demo folder
 * and the reference implementation of logging-stack in demos.
 *
 * #define LogError( X )           MyErrorLoggingFunction( X )
 * #define LogWarn( X )            MyWarnLoggingFunction( X )
 * #define LogInfo( X )            MyInfoLoggingFunction( X )
 * #define LogDebug( X )           MyDebugLoggingFunction( X )
 *
 * <b>Default values</b>: Logging is turned off, and no code is generated for logging calls
 * in the MQTT library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif
#ifndef LogWarn
    #define LogWarn( message )
#endif
#ifndef LogInfo
    #define LogInfo( message )
#endif
#ifndef LogDebug
    #define LogDebug( message )
#endif

/**
 * @brief The maximum number of MQTT PUBLISH messages that may be pending
 * acknowledgement at any time.
 *
 * QoS 1 and 2 MQTT PUBLISHes require acknowledgement from the server before
 * they can be completed. While they are awaiting the acknowledgement, the
 * client must maintain information about their state. The value of this
 * macro sets the limit on how many simultaneous PUBLISH states an MQTT
 * context maintains.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `10`
 */
#ifndef MQTT_STATE_ARRAY_MAX_COUNT
    /* Default value for the maximum acknowledgement pending PUBLISH messages. */
    #define MQTT_STATE_ARRAY_MAX_COUNT    ( 10U )
#endif

/**
 * @brief The number of retries for receiving CONNACK.
 *
 * The MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT will be used only when the
 * timeoutMs parameter of #MQTT_Connect is passed as 0 . The transport
 * receive for CONNACK will be retried MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
 * times before timing out. A value of 0 for this config will cause the
 * transport receive for CONNACK  to be invoked only once.
 *
 * <b>Possible values:</b> Any positive 16 bit integer. <br>
 * <b>Default value:</b> `5`
 */
#ifndef MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
    /* Default value for the CONNACK receive retries. */
    #define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 5U )
#endif

/**
 * @brief Number of milliseconds to wait for a ping response to a ping
 * request as part of the keep-alive mechanism.
 *
 * If a ping response is not received before this timeout, then
 * #MQTT_ProcessLoop will return #MQTTKeepAliveTimeout.
 *
 * <b>Possible values:</b> Any positive integer up to SIZE_MAX. <br>
 * <b>Default value:</b> `500`
 */
#ifndef MQTT_PINGRESP_TIMEOUT_MS
    /* Wait 0.5 seconds by default for a ping response. */
    #define MQTT_PINGRESP_TIMEOUT_MS    ( 500U )
#endif


#endif /* ifndef MQTT_CONFIG_DEFAULTS_H_ */
