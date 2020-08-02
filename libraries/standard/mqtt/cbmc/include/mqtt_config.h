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
#define LIBRARY_LOG_NAME     "MQTT"
#define LIBRARY_LOG_LEVEL    LOG_NONE

#include "logging_stack.h"

/* Mock a network context for the CBMC proofs. */
struct NetworkContext
{
    int NetworkContext;
};

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
 *
 * @note This definition must exist in order to compile. 10U is a typical value
 * used in the MQTT demos.
 */
#define MQTT_STATE_ARRAY_MAX_COUNT              ( 10U )

/**
 * @brief Retry count for reading CONNACK from network.
 *
 * The MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT will be used only when the
 * timeoutMs parameter of #MQTT_Connect() is passed as 0 . The transport
 * receive for CONNACK will be retried MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT
 * times before timing out. A value of 0 for this config will cause the
 * transport receive for CONNACK  to be invoked only once.
 */
#define MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT    ( 2U )

#endif /* ifndef MQTT_CONFIG_H_ */
