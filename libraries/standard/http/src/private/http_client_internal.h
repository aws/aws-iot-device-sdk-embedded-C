#ifndef HTTP_CLIENT_INTERNAL_H_
#define HTTP_CLIENT_INTERNAL_H_

#include "http_config.h"
#include "http_parser.h"

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
 * @brief The HTTP protocol version of this library is HTTP/1.1.
 */
#define HTTP_PROTOCOL_VERSION                   "HTTP/1.1"
#define HTTP_PROTOCOL_VERSION_LEN               ( sizeof( HTTP_PROTOCOL_VERSION ) - 1u )

/**
 * @brief Default value when pRequestInfo->pPath == NULL.
 */
#define HTTP_EMPTY_PATH                         "/"
#define HTTP_EMPTY_PATH_LEN                     ( sizeof( HTTP_EMPTY_PATH ) - 1u )

/**
 * @brief Consants for HTTP header formatting
 */
#define HTTP_HEADER_LINE_SEPARATOR              "\r\n"
#define HTTP_HEADER_LINE_SEPARATOR_LEN          ( sizeof( HTTP_HEADER_LINE_SEPARATOR ) - 1u )
#define HTTP_HEADER_END_INDICATOR               "\r\n\r\n"
#define HTTP_HEADER_END_INDICATOR_LEN           ( sizeof( HTTP_HEADER_END_INDICATOR ) - 1u )
#define HTTP_HEADER_FIELD_SEPARATOR             ": "
#define HTTP_HEADER_FIELD_SEPARATOR_LEN         ( sizeof( HTTP_HEADER_FIELD_SEPARATOR ) - 1u )
#define COLON_CHARACTER                         ":"
#define COLON_CHARACTER_LEN                     ( sizeof( COLON_CHARACTER ) - 1u )
#define SPACE_CHARACTER                         " "
#define SPACE_CHARACTER_LEN                     ( sizeof( SPACE_CHARACTER ) - 1u )
#define EQUAL_CHARACTER                         "="
#define EQUAL_CHARACTER_LEN                     ( sizeof( EQUAL_CHARACTER ) - 1u )
#define DASH_CHARACTER                          "-"
#define DASH_CHARACTER_LEN                      ( sizeof( DASH_CHARACTER ) - 1u )

/**
 * @brief Constants for header fields added automatically during the request
 * initialization.
 */
#define HTTP_USER_AGENT_FIELD                   "User-Agent"
#define HTTP_USER_AGENT_FIELD_LEN               ( sizeof( HTTP_USER_AGENT_FIELD ) - 1u )
#define HTTP_HOST_FIELD                         "Host"
#define HTTP_HOST_FIELD_LEN                     ( sizeof( HTTP_HOST_FIELD ) - 1u )
#define HTTP_USER_AGENT_VALUE_LEN               ( sizeof( HTTP_USER_AGENT_VALUE ) - 1u )

/**
 * @brief Constants for header fields added based on flags.
 */
#define HTTP_CONNECTION_FIELD                   "Connection"
#define HTTP_CONNECTION_FIELD_LEN               ( sizeof( HTTP_CONNECTION_FIELD ) - 1u )
#define HTTP_CONTENT_LENGTH_FIELD               "Content-Length"
#define HTTP_CONTENT_LENGTH_FIELD_LEN           ( sizeof( HTTP_CONTENT_LENGTH_FIELD ) - 1u )

/**
 * @brief Constants for header values added based on flags.
 */
#define HTTP_CONNECTION_KEEP_ALIVE_VALUE        "keep-alive"
#define HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN    ( sizeof( HTTP_CONNECTION_KEEP_ALIVE_VALUE ) - 1u )
#define HTTP_CONNECTION_CLOSE_VALUE             "close"
#define HTTP_CONNECTION_CLOSE_VALUE_LEN         ( sizeof( HTTP_CONNECTION_CLOSE_VALUE ) - 1u )


/**
 * @brief Constants relating to Range Requests.
 */
#define HTTP_RANGE_REQUEST_HEADER_FIELD               "Range"
#define HTTP_RANGE_REQUEST_HEADER_FIELD_LEN           ( sizeof( HTTP_RANGE_REQUEST_HEADER_FIELD ) - 1u )
#define HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX        "bytes="
#define HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN    ( sizeof( HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX ) - 1u )

/**
 * @brief The maximum buffer space for storing the Content-Length header field
 * line.
 */
#define HTTP_MAX_CONTENT_LENGTH_HEADER_LINE_LEN                          \
    ( HTTP_CONTENT_LENGTH_FIELD_LEN + HTTP_HEADER_FIELD_SEPARATOR_LEN +  \
      HTTP_HEADER_FIELD_SEPARATOR_LEN + MAX_INT32_NO_OF_DECIMAL_DIGITS + \
      HTTP_HEADER_END_INDICATOR_LEN )

/**
 * @brief Maximum value of a 32 bit signed integer is 2,147,483,647.
 *
 * Used for calculating buffer space for ASCII representation of range values.
 */
#define MAX_INT32_NO_OF_DECIMAL_DIGITS    10u

/**
 * @brief Maximum buffer space for storing a Range Request Value.
 *
 * Largest size is of the form:
 * "bytes=<Max-Integer-Value>-<<Max-Integer-Value>"
 */
#define HTTP_MAX_RANGE_REQUEST_VALUE_LEN                                            \
    ( HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN + MAX_INT32_NO_OF_DECIMAL_DIGITS + \
      1u /* Dash character '-' */ + MAX_INT32_NO_OF_DECIMAL_DIGITS )

/**
 * @brief Return value for the http-parser registered callback to signal halting
 * further execution.
 */
#define HTTP_PARSER_STOP_PARSING            1

/**
 * @brief Return value for http_parser registered callback to signal
 * continuation of HTTP response parsing.
 */
#define HTTP_PARSER_CONTINUE_PARSING        0

/**
 * @brief The minimum request-line in the headers has a possible one character
 * custom method and a single forward / or asterisk * for the path:
 *
 * <1 character custom method> <1 character / or *> HTTP/1.x\r\n\r\n
 *
 * Therefore the minimum length is 16. If this minimum request-line is not
 * satisfied, then the request headers to send are invalid.
 *
 * Note that custom methods are allowed per:
 * https://tools.ietf.org/html/rfc2616#section-5.1.1.
 */
#define HTTP_MINIMUM_REQUEST_LINE_LENGTH    16u


/**
 * @brief An aggregator that represents the user-provided parameters to the
 * #HTTPClient_ReadHeader API function. This will be used as context parameter
 * for the parsing callbacks used by the API function.
 */
typedef struct findHeaderContext
{
    const uint8_t * pField;     /**< The field that is being searched for. */
    size_t fieldLen;            /**< The length of pField. */
    const uint8_t ** pValueLoc; /**< The location of the value found in the buffer. */
    size_t * pValueLen;         /**< the length of the value found. */
    uint8_t fieldFound;         /**< Indicates that the header field was found during parsing. */
    uint8_t valueFound;         /**< Indicates that the header value was found during parsing. */
} findHeaderContext_t;

#endif /* ifndef HTTP_CLIENT_INTERNAL_H_ */
