#ifndef HTTP_CLIENT_H_
#define HTTP_CLIENT_H_

#include <stdint.h>
#include "config.h"

#include "const.h"

/**
 * @brief Maximum size, in bytes, of headers allowed from the server.
 *
 * If the total size in bytes of the headers sent from this server exceeds this
 * configuration, then the status code #HTTP_SECURITY_ALERT_HEADERS is
 * returned from #HTTPClient_Send.
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
#define HTTP_METHOD_GET     "GET"                  /**< HTTP Method GET. */
#define HTTP_METHOD_PUT     "PUT"                  /**< HTTP Method PUT. */
#define HTTP_METHOD_POST    "POST"                 /**< HTTP Method POST. */
#define HTTP_METHOD_HEAD    "HEAD"                 /**< HTTP Method HEAD. */

/**
 * Flags for #HTTPRequestInfo_t.flags.
 * These flags control what headers are written or not to the
 * #HttpRequestHeaders_t.pBuffer.
 */

/**
 * @brief Set this flag to indicate the request is for a persistent connection.
 *
 * Setting this will cause a "Connection: Keep-Alive" to be written to the
 * request.
 */
#define HTTP_REQUEST_KEEP_ALIVE_FLAG                0x1U

/**
 * @brief Set this flag to disable automatically writing the Content-Length
 * header.
 */
#define HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG    0x2U

/**
 * Flags for #HTTPResponse_t.flags.
 * These flags are populated in #HTTPResponse_t.flags by the #HTTPClient_Send()
 * function.
 */

/**
 * @brief This will be set to true if header "Connection: close" is found.
 *
 * If a "Connection: close" header is present the application should always
 * close the connection.
 */
#define HTTP_RESPONSE_CONNECTION_CLOSE_FLAG         0x1U

/**
 * @brief This will be set to true if header "Connection: Keep-Alive" is found.
 */
#define HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG    0x2U

/**
 * @brief The HTTPNetworkContext is an incomplete type. The application must
 * define HTTPNetworkContext to the type of their network context. This context
 * is passed into the network interface functions.
 */
    struct HTTPNetworkContext;
    typedef struct HTTPNetworkContext   HTTPNetworkContext_t;

/**
 * @brief Transport interface for sending data over the network.
 *
 * If the number of bytes written returned is less than bytesToWrite, then
 * #HTTPClient_Send will return HTTP_NETWORK_ERROR. If a negative value is
 * returned then this #HTTPClient_Send will also return #HTTP_NETWORK_ERROR.
 *
 * @param[in] context User defined context.
 * @param[in] pBuffer Buffer to write to the network stack.
 * @param[in] bytesToWrite Number of bytes to write to the network.
 *
 * @return The number of bytes written or a negative network error code.
 */
typedef int32_t (* HTTPTransportSend_t )( HTTPNetworkContext_t * pContext,
                                          const void * pBuffer,
                                          size_t bytesToWrite );

/**
 * @brief Transport interface for reading data on the network.
 *
 * This function will read up to bytesToRead amount of data from the network.
 * If this function returns a value less than zero, then #HTTPClient_Send will
 * return #HTTP_NETWORK_ERROR. If this function returns less than the
 * bytesToRead and greater than zero, then this function will be invoked again
 * if the data in pBuffer contains a partial HTTP response message.
 *
 * @param[in] context User defined context.
 * @param[in] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return The number of bytes read or a negative error code.
 */
typedef int32_t (* HTTPTransportRecv_t )( HTTPNetworkContext_t * pContext,
                                          void * pBuffer,
                                          size_t bytesToRead );

/**
 * @brief The HTTP Client library transport layer interface.
 */
typedef struct HTTPTransportInterface
{
    HTTPTransportRecv_t recv;
    HTTPTransportSend_t send;
    HTTPNetworkContext_t * pContext;
} HTTPTransportInterface_t;

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
    HTTP_SUCCESS = 0,

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

    HTTP_NOT_SUPPORTED,
    HTTP_PARTIAL_RESPONSE,
    HTTP_INSUFFICIENT_MEMORY,
    HTTP_INTERNAL_ERROR,
    HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED,
    HTTP_SECURITY_ALERT_PARSER_INVALID_CHARACTER,
    HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH,
    /* TODO: Add return codes as implementation continues. */
} HTTPStatus_t;

/**
 * @brief Represents header data that will be sent in an HTTP request.
 *
 * The memory for the header data buffer is supplied by the user. Information in
 * the buffer will be filled by calling #HTTPClient_InitializeRequestHeaders.
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

    /**
     * @brief Flags to activate other request header configurations.
     */
    uint32_t flags;
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
    uint32_t flags;
} HTTPRequestInfo_t;



/**
 * @brief Callback to intercept headers during the first parse through of the
 * response as it is received from the network.
 */
typedef struct httpResponseParsingCallback
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
} HTTPClient_HeaderParsingCallback_t;

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
     * This buffer is owned by the library during  #HTTPClient_Send and
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
    HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback;

    /**
     * @brief The starting location of the response headers in pBuffer.
     *
     * This is updated by #HTTPClient_Send.
     */
    uint8_t * pHeaders;

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
    uint8_t * pBody;

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
    uint32_t flags;
} HTTPResponse_t;

/**
 * @brief Initialize the request headers, stored in
 * #HTTPRequestHeaders_t.pBuffer, with initial configurations from
 * #HTTPRequestInfo_t.
 *
 * Upon return, #HTTPRequestHeaders_t.headersLen will be updated with the number
 * of bytes written if there is sufficient memory.
 *
 * Each line in the header is listed below and written in this order:
 *     <#HTTPRequestInfo_t.method> <#HTTPRequestInfo_t.pPath> <HTTP_PROTOCOL_VERSION>
 *     User-Agent: <HTTP_USER_AGENT_VALUE>
 *     Host: <#HTTPRequestInfo_t.pHost>
 *     Connection: close
 *
 * Note that Connection header value can be changed to keep-alive by setting
 * the HTTP_REQUEST_KEEP_ALIVE_FLAG in #HTTPRequestInfo_t.flags.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pRequestInfo Initial request header configurations.
 * @return One of the following:
 * - #HTTP_SUCCESS (If successful, an error code otherwise.)
 * - #HTTP_INVALID_PARAMETER (If any provided parameters and their members are NULL.)
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
 * TODO: Expand documentation.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pName The header field name to write.
 * @param[in] nameLen The byte length of the header field name.
 * @param[in] pValue The header value to write.
 * @param[in] valueLen The byte length of the header field value.
 *
 * @return #HTTP_SUCCESS if successful, an error code otherwise.
 * TODO: Update for exact error codes returned.
 */
HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pName,
                                   size_t nameLen,
                                   const char * pValue,
                                   size_t valueLen );

/**
 * @brief Add the byte range request header to the request headers store in
 * #HTTPRequestHeaders_t.pBuffer.
 *
 * For example, if requesting for the first 1kB of a file the following would be
 * written  "Range: bytes=0-1024\r\n".
 *
 * TODO: Add documentation about rangeStart and rangeEnd configuration.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] rangeStart The starting range for the requested file.
 * @param[in] rangeEnd The ending range for the requested file.
 *
 * @return #HTTP_SUCCESS if successful, an error code otherwise.
 * TODO: Update for exact error codes returned.
 */
HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStart,
                                        int32_t rangeEnd );

/**
 * @brief Send the request headers in #HTTPRequestHeaders_t and request body in
 * parameter pRequestBodyBuf over the transport. The response is received in
 * #HTTPResponse_t.
 *
 * TODO: Expand documentation.
 *
 * @param[in] pTransport Transport interface, see #HTTPTransportInterface_t for
 * more information.
 * @param[in] pRequestHeaders Request configuration containing the buffer of
 * headers to send.
 * @param[in] pRequestBodyBuf Request entity body.
 * @param[in] reqBodyBufLen The length of the request entity in bytes.
 * @param[in] pResponse The response message and some notable response
 * parameters will be returned here on success.
 *
 * @return #HTTP_SUCCESS if successful, an error code otherwise.
 * TODO: Update for exact error codes returned.
 */
HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t * pTransport,
                              const HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse );

/**
 * @brief Read a header from the completed response #HTTPResponse_t. This will
 * return the response header value location within #HTTPResponse_t.pBuffer.
 *
 * This function should be used only a completed response. A #HTTPResponse_t is
 * not complete until #HTTPClient_Send returns.
 *
 * TODO: Expand documentation.
 *
 * @param[in] pResponse Completed response.
 * @param[in] pName The header field name to read.
 * @param[in] nameLen The length of the header field name in bytes.
 * @param[out] pValue The location of the header value in
 * #HTTPResponse_t.pBuffer.
 * @param[out] valueLen The length of the header value in bytes.
 *
 * @return #HTTP_SUCCESS if successful, an error code otherwise.
 * TODO: Update for exact error codes returned.
 */
HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const char * pName,
                                    size_t nameLen,
                                    char ** pValue,
                                    size_t * valueLen );

#endif /* ifndef HTTP_CLIENT_H_ */
