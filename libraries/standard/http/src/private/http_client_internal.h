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

/**
 * @brief The HTTP protocol version of this library is HTTP/1.1.
 */
#define HTTP_PROTOCOL_VERSION                   "HTTP/1.1"
#define HTTP_PROTOCOL_VERSION_LEN               ( sizeof( HTTP_PROTOCOL_VERSION ) - 1 )

/**
 * @brief Default value when pRequestInfo->pPath == NULL.
 */
#define HTTP_EMPTY_PATH                         "/"
#define HTTP_EMPTY_PATH_LEN                     ( sizeof( HTTP_EMPTY_PATH ) - 1 )

/**
 * @brief Consants for HTTP header formatting
 */
#define HTTP_HEADER_LINE_SEPARATOR              "\r\n"
#define HTTP_HEADER_LINE_SEPARATOR_LEN          ( sizeof( HTTP_HEADER_LINE_SEPARATOR ) - 1 )
#define HTTP_HEADER_END_INDICATOR               "\r\n\r\n"
#define HTTP_HEADER_END_INDICATOR_LEN           ( sizeof( HTTP_HEADER_END_INDICATOR ) - 1 )
#define CARRIAGE_RETURN_CHARACTER               '\r'
#define NEWLINE_CHARACTER                       '\n'
#define HTTP_HEADER_FIELD_SEPARATOR             ": "
#define HTTP_HEADER_FIELD_SEPARATOR_LEN         ( sizeof( HTTP_HEADER_FIELD_SEPARATOR ) - 1 )
#define COLON_CHARACTER                         ":"
#define COLON_CHARACTER_LEN                     ( sizeof( COLON_CHARACTER ) - 1 )
#define SPACE_CHARACTER                         " "
#define SPACE_CHARACTER_LEN                     ( sizeof( SPACE_CHARACTER ) - 1 )
#define EQUAL_CHARACTER                         "="
#define EQUAL_CHARACTER_LEN                     ( sizeof( EQUAL_CHARACTER ) - 1 )
#define DASH_CHARACTER                          "-"
#define DASH_CHARACTER_LEN                      ( sizeof( DASH_CHARACTER ) - 1 )

/**
 * @brief Constants for header fields added automatically during the request initialization.
 */
#define HTTP_USER_AGENT_FIELD                   "User-Agent"
#define HTTP_USER_AGENT_FIELD_LEN               ( sizeof( HTTP_USER_AGENT_FIELD ) - 1 )
#define HTTP_HOST_FIELD                         "Host"
#define HTTP_HOST_FIELD_LEN                     ( sizeof( HTTP_HOST_FIELD ) - 1 )

/**
 * @brief Constants for header fields added based on flags.
 */
#define HTTP_CONNECTION_FIELD                   "Connection"
#define HTTP_CONNECTION_FIELD_LEN               ( sizeof( HTTP_CONNECTION_FIELD ) - 1 )
#define HTTP_CONTENT_LENGTH_FIELD               "Content-Length"
#define HTTP_CONTENT_LENGTH_FIELD_LEN           ( sizeof( HTTP_CONTENT_LENGTH_FIELD ) - 1 )

/**
 * @brief Constants for header values added based on flags.
 */
#define HTTP_CONNECTION_KEEP_ALIVE_VALUE        "keep-alive"
#define HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN    ( sizeof( HTTP_CONNECTION_KEEP_ALIVE_VALUE ) - 1 )
#define HTTP_CONNECTION_CLOSE_VALUE             "close"
#define HTTP_CONNECTION_CLOSE_VALUE_LEN         ( sizeof( HTTP_CONNECTION_CLOSE_VALUE ) - 1 )

#endif /* ifndef HTTP_CLIENT_INTERNAL_H_ */
