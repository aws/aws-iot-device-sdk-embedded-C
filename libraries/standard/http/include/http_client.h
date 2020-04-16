#ifndef HTTP_CLIENT_H_
#define HTTP_CLIENT_H_

#include <stdint.h>
#include <stdbool.h>

/**
 * @brief Maximum size, in bytes, of headers allowed from the server.
 * 
 * If the total size in bytes of the headers sent from this server exceeds this
 * configuration, then the status code #HTTP_SECURITY_ALERT_HEADERS is
 * returned from #HTTPClient_Send.
 */
#ifndef HTTP_MAX_HEADERS_BYTES
    #define HTTP_MAX_RESPONSE_HEADERS_BYTES      2048U
#endif

/**
 * @brief The HTTP header "User-Agent" value.
 * 
 * The following headerline is automatically written to
 * #HTTPRequestHeaders_t.pBuffer:
 * "User-Agent: AWS\r\n"
 */ 
#ifndef HTTP_USER_AGENT_VALUE
    #define HTTP_USER_AGENT_VALUE       "AWS"
#endif

/**
 * Supported HTTP request methods.
 */
#define HTTP_METHOD_GET                 "GET"  /**< HTTP Method GET. */
#define HTTP_METHOD_PUT                 "PUT"  /**< HTTP Method GET. */
#define HTTP_METHOD_POST                "POST" /**< HTTP Method GET. */
#define HTTP_METHOD_HEAD                "HEAD" /**< HTTP Method GET. */

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
#define HTTP_REQUEST_KEEP_ALIVE_FLAG                    0x1U
/** 
 * @brief Set this flag to disable automatically writing the Content-Length
 * header. 
 */
#define HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG   0x2U

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
#define HTTP_RESPONSE_CONNECTION_CLOSE_FLAG             0x1U
/**
 * @brief This will be set to true if header "Connection: Keep-Alive" is found.
 */
#define HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG        0x2U

/**
 * @brief The HTTPNetworkContext is an incomplete type. The application must 
 * define HTTPNetworkContext to the type of their network context. This context
 * is passed into the network interface functions.
 */
struct HTTPNetworkContext;
typedef struct HTTPNetworkContext * HTTPNetworkContext_t;

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
 * @return The number of bytes written or a negative network error code.
 */
typedef int32_t (* HTTPTransportSend_t )( HTTPNetworkContext_t context,
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
 * @return The number of bytes read or a negative error code.
 */
typedef int32_t (* HTTPTransportRecv_t )( HTTPNetworkContext_t context,
                                          const void * pBuffer, 
                                          size_t bytesToRead );

/**
 * @brief The HTTP Client library transport layer interface.
 */
typedef struct HTTPTransportInterface
{
    HTTPTransportRecv_t recv;
    HTTPTransportSend_t send;
    HTTPNetworkContext_t context;
} HTTPTransportInterface_t;

/**
 * @brief The HTTP Client library return status.
 */
typedef enum HTTPStatus
{
    HTTP_SUCCESS = 0,
    HTTP_INVALID_PARAMETER,
    HTTP_NETWORK_ERROR,
    HTTP_NOT_SUPPORTED,
    HTTP_PARTIAL_RESPONSE,
    HTTP_INSUFFICIENT_MEMORY,
    HTTP_INTERNAL_ERROR,
    HTTP_SECURITY_ALERT_TOO_MANY_HEADERS,
    HTTP_SECURITY_ALERT_PARSER_INVALID_CHARACTER,
    HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH,
    /* TODO: Add return codes as implementation continues. */
} HTTPStatus_t;

/**
 * @brief Represents header data that will be sent in an HTTP request. 
 * 
 * The memory for the header data buffer is supplied by the user. Information in
 * the buffer will be filled by calling #HTTPClient_InitializeHeaders.
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
    uint8_t* pBuffer;
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
    const char* method;
    size_t methodLen; /**< The length of the method in bytes. */
    
    /**
     * @brief The Request-URI to the objects of interest, e.g. "/path/to/item.txt".
     */
    const char* pPath;
    size_t pathLen; /**< The length of the path in bytes. */

    /**
     * @brief The server's host name, e.g. "s3.amazonaws.com".
     * 
     * The host does not have a "https://" or "http://" prepending.
     */
    const char* pHost;
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
typedef struct httpResponseParsingCallback {
    /**
     * @brief Invoked when both a header field and its associated header value are found.
     * @param[in] pContext User context.
     * @param[in] fieldLoc Location of the header field name in the response buffer.
     * @param[in] fieldLen Length in bytes of the field name.
     * @param[in] valueLoc Location of the header value in the response buffer.
     * @param[in] valueLen Length in bytes of the value.
     * @param[in] statusCode The HTTP response status-code.
     */
    void (*onHeaderCallback)( void* pContext, const char* fieldLoc, size_t fieldLen, const char* valueLoc, size_t valueLen, uint16_t statusCode );

    /* Private context for the application. */
    void *pContext;
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
    uint8_t* pBuffer;
    size_t bufferLen; /**< The length of the response buffer in bytes. */

    /**
     * @brief Optional callback for intercepting the header during the first 
     * parse through of the response as is it receive from the network.
     * Set to NULL to disable.
     */
    HTTPClient_HeaderParsingCallback_t* pHeaderParsingCallback;
    
    /**
     * @brief The starting location of the response headers in pBuffer.
     * 
     * This is updated by #HTTPClient_Send.
     */
    uint8_t* pHeaders;

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
    uint8_t* pBody;

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
 * TODO: Add through documentation.
 */
HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders, 
                                                      const HTTPRequestInfo_t * pRequestInfo );

/**
 * TODO: Add thorough documentation.
 */
HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders, 
                                   const char* pName, 
                                   size_t nameLen, 
                                   const char * pValue, 
                                   size_t valueLen );

/**
 * TODO: Add thorough documentation.
 */
HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t *pRequestHeaders,
                                            int32_t rangeStart,
                                            int32_t rangeEnd );

/**
 * TODO: Add thorough documentation.
 */
HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t* pTransport,
                              const HTTPRequestHeaders_t* pRequestHeaders,
                              const uint8_t* pRequestBodyBuf, // For a PUT or POST request.
                              size_t reqBodyBufLen,
                              HTTPResponse_t* pResponse );

/**
 * TODO: Add thorough documentation.
 */
HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t* pResponse,
                                    const char* pName,
                                    size_t nameLen,
                                    char **pValue,
                                    size_t* valueLen );

#endif