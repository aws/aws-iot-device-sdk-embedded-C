#ifndef MQTT_INTERNAL_H_
#define MQTT_INTERNAL_H_

/**
 * AWS IoT Embedded C SDK optional specific logging setup.
 */
#ifdef USE_AWS_IOT_CSDK_LOGGING
    #ifdef LOG_LEVEL_MQTT
        #define LIBRARY_LOG_LEVEL        LOG_LEVEL_MQTT
    #else
        #ifdef LOG_LEVEL_GLOBAL
            #define LIBRARY_LOG_LEVEL    LOG_LEVEL_GLOBAL
        #else
            #define LIBRARY_LOG_LEVEL    LOG_NONE
        #endif
    #endif
    #define LIBRARY_LOG_NAME             ( "MQTT" )
    #include "logging_setup.h"
#else /* ifdef USE_AWS_IOT_CSDK_LOGGING */
/* Otherwise please define logging macros in config.h. */
    #define LogError( message )
    #define LogError( format, ... )
    #define LogWarn( message )
    #define LogWarn( format, ... )
    #define LogInfo( message )
    #define LogInfo( format, ... )
    #define LogDebug( message )
    #define LogDebug( format, ... )
#endif /* ifdef USE_AWS_IOT_CSDK_LOGGING */

#endif /* ifndef MQTT_INTERNAL_H_ */
