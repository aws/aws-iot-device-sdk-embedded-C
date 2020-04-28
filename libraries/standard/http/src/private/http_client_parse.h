#ifndef HTTP_CLIENT_PARSE_H_
#define HTTP_CLIENT_PARSE_H_

#include "http_client.h"
/* #include "http_parser.h" */

/**
 * @brief The state of the response message parsed after
 * #HTTPClient_ParseResponse returns.
 */
typedef enum HTTPParsingState_t
{
    HTTP_PARSING_NONE = 0,   /**< The parser is initialized and has not started reading any message. */
    HTTP_PARSING_INCOMPLETE, /**< The parse found a partial reponse. */
    HTTP_PARSING_COMPLETE    /**< The parser found the entire response. */
} HTTPParsingState_t;

/**
 * The HTTP parsing context.
 */
typedef struct HTTPParsingContext
{
    /* http-parser dependencies will be added in the next incremental change. */
    /* Below will be un-commented when parsing is implemented. */
    #if 0
        http_parser httpParser; /**< Third-party http-parser context. */
    #endif
    HTTPParsingState_t state;   /**< The current state of the HTTP response parsed. */
    HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback;
} HTTPParsingContext_t;

/**
 * Initialize the HTTP Client response parsing context.
 *
 * @param[in] pParsingContext The state of response parsing to initialize.
 * @param[in] pHeaderParsingCallback Callback to invoked for each complete
 * header and value found.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS
 * - #HTTP_INVALID_PARAMETER
 * TODO: Other return values will be added during implementation of the parsing.
 */
HTTPStatus_t _HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                   HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback );

/**
 * Parse the input HTTP response buffer.
 *
 * This function may be invoked multiple times for different parts of the the
 * HTTP response. The state of what was last parsed in the response is kept in
 * #HTTPParsingContext_t.
 *
 * Any error found in parsing is considered a malformed response and therefore
 * a security alert. The application should close the connection with the server
 * if any HTTP_SECURITY_ALERT_X errors are returned.
 *
 * @param[in] pParsingState The state of the response parsing.
 * @param[in] pBuffer The buffer containing response message to parse.
 * @param[in] bufferLen The length in the buffer to parse.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS
 * - #HTTP_INVALID_PARAMETER
 * - #HTTP_SECURITY_ALERT_PARSER_INVALID_CHARACTER
 * TODO: Other return values are to be added during implementation of parsing.
 */
HTTPStatus_t _HTTPClient_ParseResponse( HTTPParsingContext_t * pParsingContext,
                                        uint8_t * pBuffer,
                                        size_t bufferLen );

#endif /* ifndef HTTP_CLIENT_PARSE_H_ */
