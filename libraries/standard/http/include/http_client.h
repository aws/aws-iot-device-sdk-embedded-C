#ifndef HTTP_CLIENT_H_
#define HTTP_CLIENT_H_

#include <stdint.h>
#include <stddef.h>
/* Include config file before other headers. */
#include "http_config.h"
/* Transport layer interface include. */
#include "transport_interface.h"

/**
 * @brief Maximum size, in bytes, of headers allowed from the server.
 *
 * If the total size in bytes of the headers received from the server exceeds
 * this configuration, then the status code
 * #HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED is returned from
 * #HTTPClient_Send.
 */
#ifndef HTTP_MAX_RESPONSE_HEADERS_SIZE_BYTES
    #define HTTP_MAX_RESPONSE_HEADERS_SIZE_BYTES    2048U
#endif

/**
 * @brief The HTTP header "User-Agent" value.
 *
 * The following headerline is automatically written to
 * #HTTPRequestHeaders_t.pBuffer:
 * "User-Agent: my-platform-name\r\n"
 */
#ifndef HTTP_USER_AGENT_VALUE
    #define HTTP_USER_AGENT_VALUE    "my-platform-name"
#endif

/**
 * @brief Supported HTTP request methods.
 */
#define HTTP_METHOD_GET                          "GET"  /**< HTTP Method GET. */
#define HTTP_METHOD_PUT                          "PUT"  /**< HTTP Method PUT. */
#define HTTP_METHOD_POST                         "POST" /**< HTTP Method POST. */
#define HTTP_METHOD_HEAD                         "HEAD" /**< HTTP Method HEAD. */

/**
 * @brief The maximum Content-Length header field and value that could be
 * written to the request header buffer.
 */
#define HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH    sizeof( "Content-Length: 4294967295" ) - 1u

/**
 * @section http_send_flags
 * @brief Values for #HTTPClient_Send sendFlags parameter.
 * These flags control some behavior of sending the request or receiving the
 * response.
 *
 * - #HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG <br>
 *   @copybrief HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * #HTTPClient_Send.
 */

/**
 * @brief Set this flag to disable automatically writing the Content-Length
 * header to send to the server.
 *
 * This flag is valid only for #HTTPClient_Send.sendFlags.
 */
#define HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG    0x1U

/**
 * @section http_request_flags
 * @brief Flags for #HTTPRequestInfo_t.reqFlags.
 * These flags control what headers are written or not to the
 * #HttpRequestHeaders_t.pBuffer by #HTTPClient_InitializeRequestHeaders.
 *
 * - #HTTP_REQUEST_KEEP_ALIVE_FLAG <br>
 *   @copybrief HTTP_REQUEST_KEEP_ALIVE_FLAG
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * #HTTPClient_InitializeRequestHeaders.
 */

/**
 * @brief Set this flag to indicate that the request is for a persistent
 * connection.
 *
 * Setting this will cause a "Connection: Keep-Alive" to be written to the
 * request headers.
 *
 * This flag is valid only for #HTTPRequestInfo.reqFlags.
 */
#define HTTP_REQUEST_KEEP_ALIVE_FLAG    0x1U

/**
 * @section http_response_flags
 * @brief Flags for #HTTPResponse_t.respFlags.
 * These flags are populated in #HTTPResponse_t.respFlags by the #HTTPClient_Send
 * function.
 *
 * - #HTTP_RESPONSE_CONNECTION_CLOSE_FLAG <br>
 *   @copybrief HTTP_RESPONSE_CONNECTION_CLOSE_FLAG
 * - #HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG
 *   @copybrief HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG
 */

/**
 * @brief This will be set to true if header "Connection: close" is found.
 *
 * If a "Connection: close" header is present the application should always
 * close the connection.
 *
 * This flag is valid only for #HTTPResponse_t.respFlags.
 */
#define HTTP_RESPONSE_CONNECTION_CLOSE_FLAG         0x1U

/**
 * @brief This will be set to true if header "Connection: Keep-Alive" is found.
 *
 * This flag is valid only for #HTTPResponse_t.respFlags.
 */
#define HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG    0x2U

/**
 * @brief Flag that represents End of File byte in the range specification of
 * a Range Request.
 * This flag should be used ONLY for 2 kinds of range specifications when
 * creating the Range Request header through the #HTTPClient_AddRangeHeader
 * function:
 *  - When the requested range is all bytes from the starting range byte to
 * the end of file.
 *  - When the requested range is for the last N bytes of the file.
 * In both cases, this value should be used for the "rangeEnd" parameter.
 */
#define HTTP_RANGE_REQUEST_END_OF_FILE              -1

/**
 * @brief The HTTP Client library return status.
 */
typedef enum HTTPStatus
{
    /**
     * @brief The HTTP Client library function completed successfully.
     *
     * Functions that may return this value:
     * - #HTTPClient_InitializeRequestHeaders
     * - #HTTPClient_AddHeader
     * - #HTTPClient_AddRangeHeader
     * - #HTTPClient_Send
     * - #HTTPClient_ReadHeader
     */
    HTTP_SUCCESS,

    /**
     * @brief The HTTP Client library function input an invalid parameter.
     *
     * Functions that may return this value:
     * - #HTTPClient_InitializeRequestHeaders
     * - #HTTPClient_AddHeader
     * - #HTTPClient_AddRangeHeader
     * - #HTTPClient_Send
     * - #HTTPClient_ReadHeader
     */
    HTTP_INVALID_PARAMETER,

    /**
     * @brief A network error was returned from the transport interface.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_NETWORK_ERROR,

    /**
     * @brief Part of the HTTP response was received from the network.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_PARTIAL_RESPONSE,

    /**
     * @brief No HTTP response was received from the network.
     *
     * This can occur only if there was no data received from the transport
     * interface.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_NO_RESPONSE,

    /**
     * @brief The application buffer was not large enough for the HTTP request
     * headers or the HTTP response message.
     *
     * Functions that may return this value:
     * - #HTTPClient_InitializeRequestHeaders
     * - #HTTPClient_AddHeader
     * - #HTTPClient_AddRangeHeader
     * - #HTTPClient_Send
     */
    HTTP_INSUFFICIENT_MEMORY,

    /**
     * @brief The server sent more headers than the configured
     * #HTTP_MAX_RESPONSE_HEADERS_SIZE_BYTES.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED,

    /**
     * @brief A response contained the "Connection: close" header, but there
     * was more data at the end of the complete message.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA,

    /**
     * @brief The server sent a chunk header containing an invalid character.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_INVALID_CHUNK_HEADER,

    /**
     * @brief The server sent a response with an invalid character in the
     * HTTP protocol version.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_INVALID_PROTOCOL_VERSION,

    /**
     * @brief The server sent a response with an invalid character in the
     * HTTP status-code or the HTTP status code is out of range.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_INVALID_STATUS_CODE,

    /**
     * @brief An invalid character was found in the HTTP response message.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_INVALID_CHARACTER,

    /**
     * @brief The response contains either an invalid character in the
     * Content-Length header or a Content-Length header when it was not expected
     * to be present.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     */
    HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH,

    /**
     * @brief An error occurred in the third-party parsing library.
     *
     * Functions that may return this value:
     * - #HTTPClient_Send
     * - #HTTPClient_ReadHeader
     */
    HTTP_PARSER_INTERNAL_ERROR,

    /**
     * @brief The requested header field was not found in the response buffer.
     *
     * Functions that may return this value:
     * - #HTTPClient_ReadHeader
     */
    HTTP_HEADER_NOT_FOUND,

    /**
     * @brief The HTTP response, provided for parsing, is either corrupt or
     * incomplete.
     *
     * Functions that may return this value:
     * - #HTTPClient_ReadHeader
     */
    HTTP_INVALID_RESPONSE
} HTTPStatus_t;

/**
 * @brief Represents header data that will be sent in an HTTP request.
 *
 * The memory for the header data buffer is supplied by the user. Information in
 * the buffer will be filled by calling #HTTPClient_InitializeRequestHeaders and
 * #HTTPClient_AddHeader. This buffer may be automatically filled with the
 * Content-Length header in #HTTPClient_Send, please see
 * HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH for the maximum amount of space needed
 * to accommodate the Content-Length header.
 */
typedef struct HTTPRequestHeaders
{
    /**
     * @brief Buffer to hold the raw HTTP request headers.
     *
     * This buffer is supplied by the application.
     *
     * This buffer is owned by the library during #HTTPClient_AddHeader,
     * #HTTPClient_AddRangeHeader, #HTTPClient_InitializeRequestHeaders, and
     * #HTTPClient_Send. This buffer should not be modifed until
     * after these functions return.
     *
     * For optimization this buffer may be re-used with the response. The user
     * can re-use this buffer for the storing the response from the server in
     * #HTTPResponse_t.pBuffer.
     */
    uint8_t * pBuffer;
    size_t bufferLen; /**< The length of pBuffer in bytes. */

    /**
     * @brief The actual size in bytes of headers in the buffer. This field
     * is updated by the HTTP Client library functions #HTTPClient_AddHeader,
     * and #HTTPClient_InitializeRequestHeaders.
     */
    size_t headersLen;
} HTTPRequestHeaders_t;

/**
 * @brief Configurations of the initial request headers.
 */
typedef struct HTTPRequestInfo
{
    /**
     * @brief The HTTP request method e.g. "GET", "POST", "PUT", or "HEAD".
     */
    const char * method;
    size_t methodLen; /**< The length of the method in bytes. */

    /**
     * @brief The Request-URI to the objects of interest, e.g. "/path/to/item.txt".
     */
    const char * pPath;
    size_t pathLen; /**< The length of the path in bytes. */

    /**
     * @brief The server's host name, e.g. "my-storage.my-cloud.com".
     *
     * The host does not have a "https://" or "http://" prepending.
     */
    const char * pHost;
    size_t hostLen; /**< The length of the host in bytes. */

    /**
     * @brief Flags to activate other request header configurations.
     */
    uint32_t reqFlags;
} HTTPRequestInfo_t;



/**
 * @brief Callback to intercept headers during the first parse through of the
 * response as it is received from the network.
 */
typedef struct HTTPClient_ResponseHeaderParsingCallback
{
    /**
     * @brief Invoked when both a header field and its associated header value are found.
     * @param[in] pContext User context.
     * @param[in] fieldLoc Location of the header field name in the response buffer.
     * @param[in] fieldLen Length in bytes of the field name.
     * @param[in] valueLoc Location of the header value in the response buffer.
     * @param[in] valueLen Length in bytes of the value.
     * @param[in] statusCode The HTTP response status-code.
     */
    void ( * onHeaderCallback )( void * pContext,
                                 const char * fieldLoc,
                                 size_t fieldLen,
                                 const char * valueLoc,
                                 size_t valueLen,
                                 uint16_t statusCode );

    /* Private context for the application. */
    void * pContext;
} HTTPClient_ResponseHeaderParsingCallback_t;

/**
 * @brief Represents an HTTP response.
 */
typedef struct HTTPResponse
{
    /**
     * @brief Buffer for both the raw HTTP header and body.
     *
     * This buffer is supplied by the application.
     *
     * This buffer is owned by the library during #HTTPClient_Send and
     * #HTTPClient_ReadHeader. This buffer should not be modifed until after
     * these functions return.
     *
     * For optimization this buffer may be used with the request headers. The
     * request header buffer is configured in #HTTPRequestHeaders_t.pBuffer.
     * When the same buffer is used for the request headers, #HTTPClient_Send
     * will send the headers in the buffer first, then fill the buffer with
     * the response message.
     */
    uint8_t * pBuffer;
    size_t bufferLen; /**< The length of the response buffer in bytes. */

    /**
     * @brief Optional callback for intercepting the header during the first
     * parse through of the response as is it receive from the network.
     * Set to NULL to disable.
     */
    HTTPClient_ResponseHeaderParsingCallback_t * pHeaderParsingCallback;

    /**
     * @brief The starting location of the response headers in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    const uint8_t * pHeaders;

    /**
     * @brief Byte length of the response headers in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t headersLen;

    /**
     * @brief The starting location of the response body in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    const uint8_t * pBody;

    /**
     * @brief Byte length of the body in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t bodyLen;

    /* Useful HTTP header values found. */

    /**
     * @brief The HTTP response Status-Code.
     *
     * This is updated by #HTTPClient_Send.
     */
    uint16_t statusCode;

    /**
     * @brief The value in the "Content-Length" header is returned here.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t contentLength;

    /**
     * @brief Count of the headers sent by the server.
     *
     * This is updated by #HTTPClient_Send.
     */
    size_t headerCount;

    /**
     * @brief Flags of useful headers found in the response.
     *
     * This is updated by #HTTPClient_Send.
     */
    uint32_t respFlags;
} HTTPResponse_t;

/**
 * @brief Initialize the request headers, stored in
 * #HTTPRequestHeaders_t.pBuffer, with initial configurations from
 * #HTTPRequestInfo_t. This method is expected to be called before sending a
 * new request.
 *
 * Upon return, #HTTPRequestHeaders_t.headersLen will be updated with the number
 * of bytes written.
 *
 * Each line in the header is listed below and written in this order:
 *     <#HTTPRequestInfo_t.method> <#HTTPRequestInfo_t.pPath> <HTTP_PROTOCOL_VERSION>
 *     User-Agent: <HTTP_USER_AGENT_VALUE>
 *     Host: <#HTTPRequestInfo_t.pHost>
 *
 * Note that "Connection" header can be added and set to "keep-alive" by
 * activating the HTTP_REQUEST_KEEP_ALIVE_FLAG in #HTTPRequestInfo_t.reqFlags.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pRequestInfo Initial request header configurations.
 * @return One of the following:
 * - #HTTP_SUCCESS (If successful)
 * - #HTTP_INVALID_PARAMETER (If any provided parameters or their members are invalid.)
 * - #HTTP_INSUFFICIENT_MEMORY (If provided buffer size is not large enough to hold headers.)
 */
HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo );

/**
 * @brief Add a header to the request headers stored in
 * #HTTPRequestHeaders_t.pBuffer.
 *
 * Upon return, pRequestHeaders->headersLen will be updated with the number of
 * bytes written.
 *
 * Headers are written in the following format:
 *     <pName>: <pField>\r\n\r\n
 * The trailing \r\n that denotes the end of the header lines is overwritten,
 * if it already exists in the buffer.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pField The header field name to write.
 * The data should be ISO 8859-1 (Latin-1) encoded per the HTTP standard,
 * but the API does not perform the character set validation.
 * @param[in] fieldLen The byte length of the header field name.
 * @param[in] pValue The header value to write.
 * The data should be ISO 8859-1 (Latin-1) encoded per the HTTP standard,
 * but the API does not perform the character set validation.
 * @param[in] valueLen The byte length of the header field value.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS (If successful.)
 * - #HTTP_INVALID_PARAMETER (If any provided parameters or their members are invalid.)
 * - #HTTP_INSUFFICIENT_MEMORY (If application-provided buffer is not large enough to hold headers.)
 */
HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pField,
                                   size_t fieldLen,
                                   const char * pValue,
                                   size_t valueLen );

/**
 * @brief Add the byte range request header to the request headers store in
 * #HTTPRequestHeaders_t.pBuffer.
 *
 * For example, if requesting for the first 1kB of a file the following would be
 * written  "Range: bytes=0-1023\r\n\r\n".
 *
 * The trailing "\r\n" that denotes the end of the header lines is overwritten, if it
 * already exists in the buffer.
 *
 * @note There are 3 different forms of range specification, determined by the
 * combination of @a rangeStartOrLastNBytes and @a rangeEnd parameter values:
 * 1. Request containing both parameters for the byte range [rangeStart, rangeEnd]
 * where @a rangeStartOrLastNBytes <= @a rangeEnd.
 * Example request: "Range: bytes=0-1023\r\n" for requesting bytes in the range [0, 1023].
 *
 * 2. Request for the last N bytes, represented by @p rangeStartOrlastNbytes.
 * @p rangeStartOrlastNbytes should be negative and @p rangeEnd should be
 * #HTTP_RANGE_REQUEST_END_OF_FILE.
 * Example request: "Range: bytes=-512\r\n" for requesting the last 512 bytes
 * (or bytes in the range [512, 1023] for a 1kB sized file).
 *
 * 3. Request for all bytes (till the end of byte sequence) from byte N,
 * represented by @p rangeStartOrlastNbytes.
 * @p rangeStartOrlastNbytes should be >= 0 and @p rangeEnd should be
 * #HTTP_RANGE_REQUEST_END_OF_FILE.
 * Example request: "Range: bytes=256-\r\n" for requesting all bytes after and
 * including byte 256 (or bytes in the range [256,1023] for a 1kB sized file).
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] rangeStartOrlastNbytes Represents either the starting byte
 * for a range OR the last N number of bytes in the requested file.
 * @param[in] rangeEnd The ending range for the requested file. For end of file
 * byte in Range Specifications 2. and 3., #HTTP_RANGE_REQUEST_END_OF_FILE
 * should be passed.
 *
 * @return Returns the following status codes:
 * #HTTP_SUCCESS if successful.
 * #HTTP_INVALID_PARAMETER, if input parameters are invalid, including when
 * the @p rangeStartOrlastNbytes and @p rangeEnd parameter combination is invalid.
 * #HTTP_INSUFFICIENT_MEMORY, if the passed #HTTPRequestHeaders_t.pBuffer
 * contains insufficient remaining memory for storing the range request.
 */
HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStartOrlastNbytes,
                                        int32_t rangeEnd );

/**
 * @brief Send the request headers in #HTTPRequestHeaders_t.pBuffer and request
 * body in @p pRequestBodyBuf over the transport. The response is received in
 * #HTTPResponse_t.pBuffer.
 *
 * If #HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG is not set in parameter @p sendFlags,
 * then the Content-Length to be sent to the server is automatically written to
 * @p pRequestHeaders. The Content-Length will not be written when there is
 * no request body. If there is not enough room in the buffer to write the
 * Content-Length then #HTTP_INSUFFICIENT_MEMORY is returned. Please see
 * #HTTP_MAX_CONTENT_LENGTH_HEADER_LENGTH for the maximum Content-Length header
 * field and value that could be written to the buffer.
 *
 * The application should close the connection with the server if any of the
 * following errors are returned:
 * - #HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED
 * - #HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA
 * - #HTTP_SECURITY_ALERT_INVALID_CHUNK_HEADER
 * - #HTTP_SECURITY_ALERT_INVALID_PROTOCOL_VERSION
 * - #HTTP_SECURITY_ALERT_INVALID_STATUS_CODE
 * - #HTTP_SECURITY_ALERT_INVALID_CHARACTER
 * - #HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH
 *
 * The @p pResponse returned is valid only if this function returns HTTP_SUCCESS.
 *
 * @param[in] pTransport Transport interface, see #TransportInterface_t for
 * more information.
 * @param[in] pRequestHeaders Request configuration containing the buffer of
 * headers to send.
 * @param[in] pRequestBodyBuf Optional Request entity body. Set to NULL if there
 * is no request body.
 * @param[in] reqBodyBufLen The length of the request entity in bytes.
 * @param[in] pResponse The response message and some notable response
 * parameters will be returned here on success.
 * @param[in] sendFlags Flags which modify the behavior of this function. Please
 * see @ref http_send_flags.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS (If successful.)
 * - #HTTP_INVALID_PARAMETER (If any provided parameters or their members are invalid.)
 * - #HTTP_NETWORK_ERROR (Errors in sending or receiving over the transport interface.)
 * - #HTTP_PARTIAL_RESPONSE (Part of an HTTP response was received in a partially filled response buffer.)
 * - #HTTP_NO_RESPONSE (No data was received from the transport interface.)
 * - #HTTP_INSUFFICIENT_MEMORY (The response received could not fit into the response buffer
 * or extra headers could not be sent in the request.)
 * - #HTTP_PARSER_INTERNAL_ERROR (Internal parsing error.)
 * Security alerts are listed below, please see #HTTPStatus_t for more information:
 * - #HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED
 * - #HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA
 * - #HTTP_SECURITY_ALERT_INVALID_CHUNK_HEADER
 * - #HTTP_SECURITY_ALERT_INVALID_PROTOCOL_VERSION
 * - #HTTP_SECURITY_ALERT_INVALID_STATUS_CODE
 * - #HTTP_SECURITY_ALERT_INVALID_CHARACTER
 * - #HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH
 */
HTTPStatus_t HTTPClient_Send( const TransportInterface_t * pTransport,
                              HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse,
                              uint32_t sendFlags );

/**
 * @brief Read a header from a buffer containing a complete HTTP response.
 * This will return the location of the response header value in the
 * #HTTPResponse_t.pBuffer buffer.
 *
 * @note This function should only be called on a complete HTTP response. If the
 * request is sent through the #HTTPClient_Send function, the #HTTPResponse_t is
 * incomplete until #HTTPClient_Send returns.
 *
 * @param[in] pResponse The buffer containing the completed HTTP response.
 * @param[in] pField The header field name to read.
 * @param[in] fieldLen The length of the header field name in bytes.
 * @param[out] pValueLoc This will be populated with the location of the
 * header value in the response buffer, #HTTPResponse_t.pBuffer.
 * @param[out] pValueLen This will be populated with the length of the
 * header value in bytes.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS (If successful.)
 * - #HTTP_INVALID_PARAMETER (If any provided parameters or their members are invalid.)
 * - #HTTP_HEADER_NOT_FOUND (Header is not found in the passed response buffer.)
 * - #HTTP_INVALID_RESPONSE (Provided response is not a valid HTTP response for parsing.)
 * - #HTTP_PARSER_INTERNAL_ERROR(If an error in the response parser.)
 */
HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const char * pField,
                                    size_t fieldLen,
                                    const char ** pValueLoc,
                                    size_t * pValueLen );

/**
 * @brief Error code to string conversion utility for HTTP Client library.
 *
 * @note This returns constant strings, which should not be modified.
 *
 * @param[in] status The status code to convert to a string.
 *
 * @return The string representation of the status code.
 */
const char * HTTPClient_strerror( HTTPStatus_t status );

#endif /* ifndef HTTP_CLIENT_H_ */
