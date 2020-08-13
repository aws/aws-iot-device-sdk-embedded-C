#ifndef MQTT_CONFIG_H_
#define MQTT_CONFIG_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging related header files are required to be included in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define LIBRARY_LOG_NAME and  LIBRARY_LOG_LEVEL.
 * 3. Include the header file "logging_stack.h".
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Configure name and log level for the MQTT library. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "MQTT"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_ERROR
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

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
#define MQTT_STATE_ARRAY_MAX_COUNT              10U

/**
 * @brief MQTT client identifier.
 *
 * No two clients may use the same client identifier simultaneously.
 */
#define MQTT_CLIENT_IDENTIFIER                  "testclient"

/**
 * @brief Retry count for reading CONNACK from network.
 *
 * #MQTT_Connect() can be using retries. If timeout passed as 0 to MQTT_Connect(),
 * retries are used to attempt to read from network. The maximum retry count is
 * specified by this config.
 */
#define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 2U )

/**
 * @brief Number of milliseconds to wait for a ping response to a ping
 * request as part of the keep-alive mechanism.
 *
 * If a ping response is not received before this timeout, then
 * #MQTT_ProcessLoop will return #MQTTKeepAliveTimeout.
 */
#define MQTT_PINGRESP_TIMEOUT_MS                ( 1000U )

/* Set network context to double pointer to buffer (uint8_t**).  */
struct NetworkContext
{
    uint8_t ** buffer;
};

#endif /* ifndef MQTT_CONFIG_H_ */
