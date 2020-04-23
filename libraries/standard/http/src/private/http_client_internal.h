#ifndef HTTP_CLIENT_INTERNAL_H_
#define HTTP_CLIENT_INTERNAL_H_

/**
 * AWS IoT Embedded C SDK optional specific logging setup.
 */
#ifdef USE_AWS_IOT_CSDK_LOGGING
    #ifdef IOT_LOG_LEVEL_HTTP
        #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_HTTP
    #else
        #ifdef IOT_LOG_LEVEL_GLOBAL
            #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
        #else
            #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
        #endif
    #endif
    #define LIBRARY_LOG_NAME             ( "HTTP" )
    #include "iot_logging_setup.h"
#else /* ifdef USE_AWS_IOT_CSDK_LOGGING */
/* Otherwise please define logging macros in config.h. */
    #define IotLogError( message )
    #define IotLogErrorWithArgs( format, ... )
    #define IotLogWarn( message )
    #define IotLogWarnWithArgs( format, ... )
    #define IotLogInfo( message )
    #define IotLogInfoWithArgs( format, ... )
    #define IotLogDebug( message )
    #define IotLogDebugWithArgs( format, ... )
#endif /* ifdef USE_AWS_IOT_CSDK_LOGGING */

#endif /* ifndef HTTP_CLIENT_INTERNAL_H_ */
