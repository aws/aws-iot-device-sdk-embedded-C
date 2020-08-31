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

/************ End of logging configuration ****************/

/* Set network context to a socket (int). This is a stub and passed through to
 * the application defined transport send and receive. */
typedef int NetworkContext_t;

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
#define MQTT_STATE_ARRAY_MAX_COUNT    ( 10U )

#endif /* ifndef MQTT_CONFIG_H_ */
