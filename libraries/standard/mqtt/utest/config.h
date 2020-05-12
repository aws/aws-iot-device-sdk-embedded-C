#ifndef CONFIG_H
#define CONFIG_H

#define IOT_LOG_LEVEL_HTTP          IOT_LOG_DEBUG

#define USE_AWS_IOT_CSDK_LOGGING    1

#ifdef USE_AWS_IOT_CSDK_LOGGING

/* Include file for POSIX reference implementation. */
    #include "iot_logging.h"

/* Define the IotLog logging interface to enable logging.
 * This demo maps the macro to the reference POSIX implementation for logging.
 * Note: @ref LIBRARY_LOG_NAME adds the name of the library, that produces the
 * log, as metadata in each log message. */
    #define IotLog( messageLevel, pFormat, ... ) \
    IotLog_Generic( messageLevel,                \
                    "[%s:%d] [%s] "pFormat,      \
                    __FILE__,                    \
                    __LINE__,                    \
                    LIBRARY_LOG_NAME,            \
                    __VA_ARGS__ )

#endif /* ifdef USE_AWS_IOT_CSDK_LOGGING */


/* Set network context to socket (int). */
typedef int MQTTNetworkContext_t;

/**
 * @brief The maximum number of MQTT PUBLISH messages that may be pending
 * acknowledgement at any time.
 *
 * QoS 1 and 2 MQTT PUBLISHes require acknowlegement from the server before
 * they can be completed. While they are awaiting the acknowledgement, the
 * client must maintain information about their state. The value of this
 * macro sets the limit on how many simultaneous PUBLISH states an MQTT
 * context maintains.
 */
#define MQTT_MAX_QUEUED_PUBLISH_MESSAGES    10

/**
 * @brief The maximum number of MQTT PUBLISH messages that may be pending
 * acknowledgement at any time.
 *
 * QoS 1 and 2 MQTT PUBLISHes require acknowledgement from the server before
 * they can be completed. While they are awaiting the acknowledgement, the
 * client must maintain information about their state. The value of this
 * macro sets the limit on how many simultaneous PUBLISH states an MQTT
 * context maintains.
 */
#define MQTT_STATE_ARRAY_MAX_COUNT          10U

/**
 * @brief MQTT client identifier.
 *
 * No two clients may use the same client identifier simultaneously.
 */
#define CLIENT_IDENTIFIER                   "testclient"


#endif /* ifndef CONFIG_H */
