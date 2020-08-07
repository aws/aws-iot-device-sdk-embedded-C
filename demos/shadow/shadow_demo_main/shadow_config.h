#ifndef SHADOW_CONFIG_H__
#define SHADOW_CONFIG_H__

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

/* Configure name and log level for the Shadow library. */
#define LIBRARY_LOG_NAME     "SHADOW_DEMO"
#define LIBRARY_LOG_LEVEL    LOG_INFO

#include "logging_stack.h"

/************ End of logging configuration ****************/

#endif /* ifndef SHADOW_CONFIG_H__ */
