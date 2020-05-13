#ifndef CONFIG_H
#define CONFIG_H

#define LOG_LEVEL_HTTP    LOG_DEBUG

#ifdef USE_CSDK_LOGGING

/* Include file for POSIX reference implementation. */
    #include "logging.h"

/* Define the IotLog logging interface to enable logging.
 * This demo maps the macro to the reference POSIX implementation for logging.
 * Note: @ref LIBRARY_LOG_NAME adds the name of the library, that produces the
 * log, as metadata in each log message. */
    #define SdkLog( messageLevel, pFormat, ... ) \
    Log_Generic( messageLevel,                   \
                 "[%s:%d] [%s] "pFormat,         \
                 __FILE__,                       \
                 __LINE__,                       \
                 LIBRARY_LOG_NAME,               \
                 __VA_ARGS__ )

#endif /* ifdef USE_CSDK_LOGGING */

#endif /* ifndef CONFIG_H */
