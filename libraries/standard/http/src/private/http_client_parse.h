#ifndef HTTP_CLIENT_PARSE_H_
#define HTTP_CLIENT_PARSE_H_

#include "http_client.h"

/**
 * @brief The state of the response message parsed after
 * #HTTPClient_ParseResponse returns.
 */
typedef enum HTTPParsingState_t
{
    HTTP_PARSING_NONE = 0,   /**< The parser has not started reading any response. */
    HTTP_PARSING_INCOMPLETE, /**< The parser found a partial reponse. */
    HTTP_PARSING_COMPLETE    /**< The parser found the entire response. */
} HTTPParsingState_t;

/**
 * @brief The HTTP response parsing context.
 */
typedef struct HTTPParsingContext
{
    /* http-parser dependencies will be added in the next incremental change. */
    /* Below will be un-commented when parsing is implemented. */
    #if 0
        http_parser httpParser;                                  /**< Third-party http-parser context. */
    #endif
    HTTPParsingState_t state;                                    /**< The current state of the HTTP response parsed. */
    HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback; /**< Callback to invoke with each header found. */
} HTTPParsingContext_t;

/**
 * @brief Initialize the HTTP Client response parsing context.
 *
 * @param[in,out] pParsingContext The parsing context to initialize.
 * @param[in] pHeaderParsingCallback Callback that will be invoked for each
 * header and value pair found.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS
 * - #HTTP_INVALID_PARAMETER
 * TODO: Other return values will be added during implementation of the parsing.
 */
HTTPStatus_t HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                  HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback );

/**
 * Parse the input HTTP response buffer.
 *
 * This function may be invoked multiple times for different parts of the the
 * HTTP response. The state of what was last parsed in the response is kept in
 * #HTTPParsingContext_t.
 *
 * The application should close the connection with the server if any
 * HTTP_SECURITY_ALERT_X errors are returned.
 * TODO: List all the security alerts possible after parsing development.
 *
 * @param[in,out] pParsingState The state of the response parsing.
 * @param[in] pBuffer The buffer containing response message to parse.
 * @param[in] bufferLen The length in the buffer to parse.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS
 * - #HTTP_INVALID_PARAMETER
 * - #HTTP_SECURITY_ALERT_PARSER_INVALID_CHARACTER
 * TODO: Other return values are to be added during implementation of parsing.
 */
HTTPStatus_t HTTPClient_ParseResponse( HTTPParsingContext_t * pParsingContext,
                                       const uint8_t * pBuffer,
                                       size_t bufferLen );

/**
 * @brief Find the specified header field in the response buffer.
 *
 * @param[in] pParsingContext The state of the of the response parsing.
 * @param[in] pBuffer The response buffer to parse.
 * @param[in] bufferLen The length of the response buffer to parse.
 * @param[in] pField The header field to search for.
 * @param[in] fieldLen The length of pField.
 * @param[out] pValue The location of the the header value found in pBuffer.
 * @param[out] valueLen The length of pValue.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS when header is found in the response.
 * - #HTTP_HEADER_NOT_FOUND if requested header is not found in response.
 * - #HTTP_INTERNAL_ERROR for any parsing errors.
 */
HTTPStatus_t HTTPClient_FindHeaderInResponse( HTTPParsingContext_t * pParsingContext,
                                              const uint8_t * pBuffer,
                                              size_t bufferLen,
                                              const uint8_t * pField,
                                              size_t fieldLen,
                                              const uint8_t ** pValue,
                                              size_t * valueLen );


#endif /* ifndef HTTP_CLIENT_PARSE_H_ */
