#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"
/* Private includes for internal macros. */
#include "private/http_client_internal.h"

#include "mock_http_parser.h"

/* Template HTTP request for a HEAD request. */
#define HTTP_TEST_REQUEST_HEAD_HEADERS         \
    "HEAD /somedir/somepage.html HTTP/1.1\r\n" \
    "test-header0: test-value0\r\n"            \
    "test-header1: test-value1\r\n"            \
    "test-header2: test-value2\r\n"            \
    "test-header3: test-value0\r\n"            \
    "test-header4: test-value1\r\n"            \
    "test-header5: test-value2\r\n"            \
    "\r\n"
#define HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH    ( sizeof( HTTP_TEST_REQUEST_HEAD_HEADERS ) - 1U )

/* Template HTTP request for a PUT request. */
#define HTTP_TEST_REQUEST_PUT_HEADERS         \
    "PUT /somedir/somepage.html HTTP/1.1\r\n" \
    "test-header1: test-value1\r\n"           \
    "test-header2: test-value2\r\n"           \
    "test-header3: test-value0\r\n"           \
    "test-header4: test-value1\r\n"           \
    "test-header5: test-value2\r\n"           \
    "\r\n"
#define HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH                    ( sizeof( HTTP_TEST_REQUEST_PUT_HEADERS ) - 1U )
#define HTTP_TEST_REQUEST_PUT_BODY                              "abcdefghijklmnopqrstuvwxyz"
#define HTTP_TEST_REQUEST_PUT_BODY_LENGTH                       ( sizeof( HTTP_TEST_REQUEST_PUT_BODY ) - 1U )
#define HTTP_TEST_REQUEST_PUT_CONTENT_LENGTH_EXPECTED           "Content-Length: 26\r\n" HTTP_HEADER_LINE_SEPARATOR
#define HTTP_TEST_REQUEST_PUT_CONTENT_LENGTH_EXPECTED_LENGTH    ( sizeof( HTTP_TEST_REQUEST_PUT_CONTENT_LENGTH_EXPECTED ) - 1U )

/* Template HTTP request for a GET request. */
#define HTTP_TEST_REQUEST_GET_HEADERS         \
    "GET /somedir/somepage.html HTTP/1.1\r\n" \
    "test-header1: test-value1\r\n"           \
    "test-header2: test-value2\r\n"           \
    "test-header3: test-value0\r\n"           \
    "test-header4: test-value1\r\n"           \
    "test-header5: test-value2\r\n"           \
    "\r\n"
#define HTTP_TEST_REQUEST_GET_HEADERS_LENGTH               ( sizeof( HTTP_TEST_REQUEST_GET_HEADERS ) - 1U )

/* HTTP OK Status-Line. */
#define HTTP_STATUS_LINE_OK                                "HTTP/1.1 200 OK\r\n"
#define HTTP_STATUS_CODE_OK                                200

/* Various header lines for test response templates. */
#define HTTP_TEST_CONTENT_LENGTH_HEADER_LINE               "Content-Length: 43\r\n"
#define HTTP_TEST_DATE_HEADER_LINE                         "Date: Sun, 14 Jul 2019 06:07:52 GMT\r\n"
#define HTTP_TEST_ETAG_HEADER_LINE                         "ETag: \"3356-5233\"\r\n"
#define HTTP_TEST_VARY_HEADER_LINE                         "Vary: *\r\n"
#define HTTP_TEST_P3P_HEADER_LINE                          "P3P: CP=\"This is not a P3P policy\"\r\n"
#define HTTP_TEST_XSERVER_HEADER_LINE                      "xserver: www1021\r\n"
#define HTTP_TEST_CONNECTION_CLOSE_HEADER_LINE             "Connection: close\r\n"
#define HTTP_TEST_CONNECTION_KEEP_ALIVE_HEADER_LINE        "Connection: keep-alive\r\n"
#define HTTP_TEST_TRANSFER_ENCODING_CHUNKED_HEADER_LINE    "Transfer-Encoding: chunked\r\n"

/* Partial header field and value for testing partial header field and value
 * handling in parser callback. */
#define HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_FIELD      "Content-Len"
#define HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_VALUE      "Content-Length: 4"

/* Template HTTP HEAD response. */
#define HTTP_TEST_RESPONSE_HEAD            \
    HTTP_STATUS_LINE_OK                    \
    HTTP_TEST_CONTENT_LENGTH_HEADER_LINE   \
    HTTP_TEST_CONNECTION_CLOSE_HEADER_LINE \
    HTTP_TEST_DATE_HEADER_LINE             \
    HTTP_TEST_ETAG_HEADER_LINE             \
    HTTP_TEST_VARY_HEADER_LINE             \
    HTTP_TEST_P3P_HEADER_LINE              \
    HTTP_TEST_XSERVER_HEADER_LINE HTTP_HEADER_LINE_SEPARATOR
#define HTTP_TEST_RESPONSE_HEAD_LENGTH                         ( sizeof( HTTP_TEST_RESPONSE_HEAD ) - 1U )
#define HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT                   7
#define HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH                 43
#define HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_FIELD_LENGTH    ( sizeof( HTTP_STATUS_LINE_OK ) + sizeof( HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_FIELD ) - 2U )
#define HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH    ( sizeof( HTTP_STATUS_LINE_OK ) + sizeof( HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_VALUE ) - 2U )

/* Template HTTP PUT response. This has no body. */
#define HTTP_TEST_RESPONSE_PUT                  \
    HTTP_STATUS_LINE_OK                         \
    HTTP_TEST_CONNECTION_KEEP_ALIVE_HEADER_LINE \
    HTTP_TEST_DATE_HEADER_LINE                  \
    HTTP_TEST_ETAG_HEADER_LINE                  \
    HTTP_TEST_VARY_HEADER_LINE                  \
    HTTP_TEST_P3P_HEADER_LINE                   \
    HTTP_TEST_XSERVER_HEADER_LINE HTTP_HEADER_LINE_SEPARATOR
#define HTTP_TEST_RESPONSE_PUT_LENGTH          ( sizeof( HTTP_TEST_RESPONSE_PUT ) - 1U )
#define HTTP_TEST_RESPONSE_PUT_HEADER_COUNT    6

/* Template HTTP GET response. */
#define HTTP_TEST_RESPONSE_GET \
    HTTP_TEST_RESPONSE_HEAD    \
    "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopq"
#define HTTP_TEST_RESPONSE_GET_LENGTH                 ( sizeof( HTTP_TEST_RESPONSE_GET ) - 1U )
#define HTTP_TEST_RESPONSE_GET_HEADER_COUNT           HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT
#define HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH         ( HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) )
#define HTTP_TEST_RESPONSE_GET_BODY_LENGTH            HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH
#define HTTP_TEST_RESPONSE_GET_CONTENT_LENGTH         HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH
#define HTTP_TEST_RESPONSE_GET_PARTIAL_BODY_LENGTH    ( HTTP_TEST_RESPONSE_GET_LENGTH - 13U )

/* Template HTTP transfer-encoding chunked response. */
#define HTTP_TEST_RESPONSE_CHUNKED                           \
    HTTP_STATUS_LINE_OK                                      \
    HTTP_TEST_TRANSFER_ENCODING_CHUNKED_HEADER_LINE          \
    HTTP_TEST_CONNECTION_KEEP_ALIVE_HEADER_LINE              \
    HTTP_TEST_DATE_HEADER_LINE                               \
    HTTP_TEST_ETAG_HEADER_LINE                               \
    HTTP_TEST_VARY_HEADER_LINE                               \
    HTTP_TEST_P3P_HEADER_LINE                                \
    HTTP_TEST_XSERVER_HEADER_LINE HTTP_HEADER_LINE_SEPARATOR \
    "b\r\n"                                                  \
    "abcdefghijk\r\n"                                        \
    "c\r\n"                                                  \
    "lmnopqrstuvw\r\n"                                       \
    "3\r\n"                                                  \
    "xyz\r\n"                                                \
    "0\r\n"                                                  \
    "\r\n"
#define HTTP_TEST_RESPONSE_CHUNKED_LENGTH          ( sizeof( HTTP_TEST_RESPONSE_CHUNKED ) - 1U )
#define HTTP_TEST_RESPONSE_CHUNKED_HEADER_COUNT    7
#define HTTP_TEST_RESPONSE_CHUNKED_BODY_LENGTH     26
#define HTTP_TEST_RESPONSE_CHUNKED_HEADERS_LENGTH               \
    sizeof( HTTP_TEST_TRANSFER_ENCODING_CHUNKED_HEADER_LINE ) + \
    sizeof( HTTP_TEST_CONNECTION_KEEP_ALIVE_HEADER_LINE ) +     \
    sizeof( HTTP_TEST_DATE_HEADER_LINE ) +                      \
    sizeof( HTTP_TEST_ETAG_HEADER_LINE ) +                      \
    sizeof( HTTP_TEST_VARY_HEADER_LINE ) +                      \
    sizeof( HTTP_TEST_P3P_HEADER_LINE ) +                       \
    sizeof( HTTP_TEST_XSERVER_HEADER_LINE ) +                   \
    HTTP_HEADER_LINE_SEPARATOR_LEN - 7U

/* Template HTTP response with no headers. */
#define HTTP_TEST_RESPONSE_NO_HEADERS \
    HTTP_STATUS_LINE_OK HTTP_HEADER_LINE_SEPARATOR
#define HTTP_TEST_RESPONSE_NO_HEADERS_LENGTH    ( sizeof( HTTP_TEST_RESPONSE_NO_HEADERS ) - 1U )

/* Test buffer to share among the test. */
#define HTTP_TEST_BUFFER_LENGTH                 1024
static uint8_t httpBuffer[ HTTP_TEST_BUFFER_LENGTH ] = { 0 };

/* Tests are run sequentially. If a response has these variables, then they
 * will be set during the onHeaderCallback(). */
static uint8_t hasConnectionClose = 0;
static uint8_t hasConnectionKeepAlive = 0;
static size_t contentLength = 0;

/* The count of times a test invoked the onHeaderCallback(). */
static uint8_t headerCallbackCount = 0;

/* The count of times a test invoked the transport send interface. */
static uint8_t sendCurrentCall = 0;
/* Set this to 1 to enable checking that the Content-Length header generated is correct. */
static uint8_t checkContentLength = 0;

/* The test sets this variable to indicate at which call count of transport send
 * to return an error from. */
static uint8_t sendErrorCall = 0;

/* The test sets this variable to indicate at which call count of transport send
 * to send less bytes than indicated. */
static uint8_t sendPartialCall = 0;

/* The network data to receive. */
static uint8_t * pNetworkData = NULL;
/* The length of the network data to receive. */
static size_t networkDataLen = 0;

/* The number of bytes to send in the first call to the transport receive
 * interface. */
static size_t firstPartBytes = 0;
/* The count of times a test invoked the transport receive interface. */
static uint8_t recvCurrentCall = 0;

/* The test sets this variable to indcate which call count count of transport
 * receive to return an error from. */
static uint8_t recvStopCall = 0;
/* The count of times a mocked http_parser_execute callback has been invoked. */
static uint8_t httpParserExecuteCallCount;

/* The error to set to the parsing context when the http_parser_execute_error
 * callback is invoked. */
static enum http_errno httpParsingErrno;

/* Response shared among the tests. */
static HTTPResponse_t response = { 0 };
/* Transport interface shared among the tests. */
static HTTPTransportInterface_t transportInterface = { 0 };
/* Request headers shared among the tests. */
static HTTPRequestHeaders_t requestHeaders = { 0 };
/* Header parsing callback shared among the tests. */
static HTTPClient_ResponseHeaderParsingCallback_t headerParsingCallback = { 0 };

/* Application callback for intercepting the headers during the parse of a new
 * response from the mocked network interface. */
static void onHeaderCallback( void * pContext,
                              const char * fieldLoc,
                              size_t fieldLen,
                              const char * valueLoc,
                              size_t valueLen,
                              uint16_t statusCode )
{
    ( void ) pContext;
    ( void ) statusCode;

    if( strncmp( fieldLoc, "Connection", fieldLen ) == 0 )
    {
        if( strncmp( valueLoc, "keep-alive", valueLen ) == 0 )
        {
            hasConnectionKeepAlive = 1;
        }
        else if( strncmp( valueLoc, "close", valueLen ) == 0 )
        {
            hasConnectionClose = 1;
        }
    }
    else if( strncmp( fieldLoc, "Content-Length", fieldLen ) == 0 )
    {
        contentLength = strtoul( valueLoc, NULL, 10 );
    }

    headerCallbackCount++;
}

/* Successful application transport send interface. */
static int32_t transportSendSuccess( HTTPNetworkContext_t * pContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    ( void ) pContext;

    if( checkContentLength == 1U )
    {
        if( sendCurrentCall == 0U )
        {
            size_t contentLengthAndHeaderEndLen = HTTP_TEST_REQUEST_PUT_CONTENT_LENGTH_EXPECTED_LENGTH;
            char * pContentLengthStart = ( ( ( char * ) pBuffer ) + bytesToWrite ) - contentLengthAndHeaderEndLen;
            TEST_ASSERT_GREATER_OR_EQUAL( contentLengthAndHeaderEndLen, bytesToWrite );
            TEST_ASSERT_EQUAL_MEMORY( HTTP_TEST_REQUEST_PUT_CONTENT_LENGTH_EXPECTED,
                                      pContentLengthStart,
                                      HTTP_TEST_REQUEST_PUT_CONTENT_LENGTH_EXPECTED_LENGTH );
        }
    }

    sendCurrentCall++;
    return bytesToWrite;
}

/* Application transport send interface that returns a network error depending
* on the call count. Set sendErrorCall to 0 to return an error on the
* first call. Set sendErrorCall to 1 to return an error on the second call. */
static int32_t transportSendNetworkError( HTTPNetworkContext_t * pContext,
                                          const void * pBuffer,
                                          size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;
    int32_t retVal = bytesToWrite;

    if( sendErrorCall == sendCurrentCall )
    {
        retVal = -1;
    }

    sendCurrentCall++;
    return retVal;
}

/* Application transport send interface that returns less bytes than expected
 * depending on the call count. Set sendPartialCall to 0 to return less bytes on
 * the first call. Set sendPartialCall to 1 to return less bytes on the second
 * call. */
static int32_t transportSendLessThanBytesToWrite( HTTPNetworkContext_t * pContext,
                                                  const void * pBuffer,
                                                  size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;
    int32_t retVal = bytesToWrite;

    if( sendPartialCall == sendCurrentCall )
    {
        retVal -= 1;
    }

    sendCurrentCall++;
    return retVal;
}

/* Application transport send that writes more bytes than expected. */
static int32_t transportSendMoreThanBytesToWrite( HTTPNetworkContext_t * pContext,
                                                  const void * pBuffer,
                                                  size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;

    return( bytesToWrite + 1 );
}


/* Application transport receive interface that sends the bytes specified in
 * firstPartBytes on the first call, then sends the rest of the response in the
 * second call. The response to send is set in pNetworkData and the current
 * call count is kept track of in recvCurrentCall. This function will return
 * zero (timeout condition) when recvStopCall matches recvCurrentCall. */
static int32_t transportRecvSuccess( HTTPNetworkContext_t * pContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pContext;
    size_t bytesToCopy = 0;

    /* To test stopping in the middle of a response message, check that the
     * flags are set. */
    if( recvStopCall == recvCurrentCall )
    {
        return 0;
    }

    /* If this is the first call, then copy the specific first bytes. */
    if( recvCurrentCall == 0 )
    {
        bytesToCopy = firstPartBytes;
    }
    /* Otherwise copy the rest of the network data. */
    else
    {
        bytesToCopy = networkDataLen;
    }

    if( bytesToCopy > bytesToRead )
    {
        bytesToCopy = bytesToRead;
    }

    memcpy( pBuffer, pNetworkData, bytesToCopy );
    pNetworkData += bytesToCopy;
    networkDataLen -= bytesToCopy;
    recvCurrentCall++;
    return bytesToCopy;
}

/* Application transport receive that return a network error. */
static int32_t transportRecvNetworkError( HTTPNetworkContext_t * pContext,
                                          void * pBuffer,
                                          size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;
    ( void ) bytesToRead;

    return -1;
}

/* Application transport receive that returns more bytes read than expected. */
static int32_t transportRecvMoreThanBytesToRead( HTTPNetworkContext_t * pContext,
                                                 void * pBuffer,
                                                 size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;

    return( bytesToRead + 1 );
}

/* Mocked http_parser_execute callback that sets the internal http_errno. */
static size_t http_parser_execute_error( http_parser * pParser,
                                         const http_parser_settings * pSettings,
                                         const char * pData,
                                         size_t len,
                                         int cmock_num_calls )
{
    ( void ) pSettings;
    ( void ) pData;
    ( void ) len;
    ( void ) cmock_num_calls;

    pParser->http_errno = httpParsingErrno;
    return 0;
}

/* Mock helper that parses the status line starting from pNext. */
static void helper_parse_status_line( const char ** pNext,
                                      http_parser * pParser,
                                      const http_parser_settings * pSettings )
{
    const char * pReasonPhraseStart = NULL;
    size_t reasonPhraseStartLen = 0;

    /* For purposes of unit testing the response is well formed in the non-error
     * cases, so the reason-phrase is always after HTTP/1.1 and the three digit
     * status code. strstr() is used only for unit testing where test input are \
     * always string literals. strstr() should not be used in application code. */
    *pNext = strstr( *pNext, SPACE_CHARACTER ); /* Get the space before the status-code. */
    *pNext += SPACE_CHARACTER_LEN;
    *pNext = strstr( *pNext, SPACE_CHARACTER ); /* Get the space before the reason-phrase. */
    *pNext += SPACE_CHARACTER_LEN;
    pReasonPhraseStart = *pNext;
    *pNext = strstr( *pNext, HTTP_HEADER_LINE_SEPARATOR );
    reasonPhraseStartLen = ( size_t ) ( *pNext - pReasonPhraseStart );
    pParser->status_code = 200;
    pSettings->on_status( pParser,
                          pReasonPhraseStart,
                          reasonPhraseStartLen );

    *pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
}

/* Mock helper that parses all of the headers starting from pNext. */
static void helper_parse_headers( const char ** pNext,
                                  http_parser * pParser,
                                  const http_parser_settings * pSettings )
{
    const char * pHeaderFieldStart = NULL;
    size_t headerFieldLen = 0;
    const char * pHeaderValueStart = NULL;
    size_t headerValueLen = 0;

    while( **pNext != '\r' )
    {
        pHeaderFieldStart = *pNext;
        *pNext = strstr( *pNext, HTTP_HEADER_FIELD_SEPARATOR );
        headerFieldLen = ( size_t ) ( *pNext - pHeaderFieldStart );
        pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

        *pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

        pHeaderValueStart = *pNext;
        *pNext = strstr( *pNext, HTTP_HEADER_LINE_SEPARATOR );
        headerValueLen = ( size_t ) ( *pNext - pHeaderValueStart );
        pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

        *pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
    }
}

/* Mock helper that parses the end of the headers starting from pNext. pNext
 * will point to the start of the body after this is finished. */
static void helper_parse_headers_finish( const char ** pNext,
                                         http_parser * pParser,
                                         const http_parser_settings * pSettings,
                                         uint8_t * isHeadResponse )
{
    uint8_t isHeadResponseReturned = 0;

    pParser->content_length = contentLength;

    if( hasConnectionClose )
    {
        pParser->flags |= F_CONNECTION_CLOSE;
    }

    if( hasConnectionKeepAlive )
    {
        pParser->flags |= F_CONNECTION_KEEP_ALIVE;
    }

    isHeadResponseReturned = pSettings->on_headers_complete( pParser );

    if( isHeadResponse != NULL )
    {
        *isHeadResponse = isHeadResponseReturned;
    }

    *pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
}

/* Mock helper that parses the response body starting from pNext. */
static void helper_parse_body( const char ** pNext,
                               http_parser * pParser,
                               const http_parser_settings * pSettings,
                               uint8_t isHeadResponse,
                               const char * pData,
                               size_t len )
{
    const char * pBody = NULL;
    size_t bodyLen = 0;

    pBody = *pNext;

    if( isHeadResponse == 0 )
    {
        bodyLen = ( size_t ) ( len - ( size_t ) ( pBody - pData ) );

        if( bodyLen > 0 )
        {
            pSettings->on_body( pParser, pBody, bodyLen );
        }
    }
}

/* Mocked http_parser_execute callback that expects a whole response to be in
 * the given data to parse. */
static size_t http_parser_execute_whole_response( http_parser * pParser,
                                                  const http_parser_settings * pSettings,
                                                  const char * pData,
                                                  size_t len,
                                                  int cmock_num_calls )
{
    ( void ) cmock_num_calls;
    const char * pNext = pData;
    uint8_t isHeadResponse = 0;

    pSettings->on_message_begin( pParser );

    helper_parse_status_line( &pNext, pParser, pSettings );
    helper_parse_headers( &pNext, pParser, pSettings );
    helper_parse_headers_finish( &pNext, pParser, pSettings, &isHeadResponse );
    helper_parse_body( &pNext, pParser, pSettings, isHeadResponse, pData, len );

    pSettings->on_message_complete( pParser );

    httpParserExecuteCallCount++;
    return len;
}

/* Mocked http_parser_execute callback that will be called the first time on the
 * response message up to the middle of the first header field, then the second
 * time on the response message from the middle of the first header field to the
 * end. */
static size_t http_parser_execute_partial_header_field( http_parser * pParser,
                                                        const http_parser_settings * pSettings,
                                                        const char * pData,
                                                        size_t len,
                                                        int cmock_num_calls )
{
    ( void ) cmock_num_calls;
    const char * pNext = pData;
    uint8_t isHeadResponse = 0;
    const char * pHeaderFieldStart = NULL;
    size_t headerFieldLen = 0;

    if( httpParserExecuteCallCount == 0 )
    {
        pSettings->on_message_begin( pParser );

        helper_parse_status_line( &pNext, pParser, pSettings );

        /* pNext now points to the start of the partial header field. */
        pHeaderFieldStart = pNext;
        headerFieldLen = len - ( size_t ) ( pHeaderFieldStart - pData );
        pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );
    }
    else
    {
        /* For testing of invoking http_parser_execute() with a parsing length
         * of zero, when data had been previously parsed. */
        if( len == 0 )
        {
            pParser->http_errno = HPE_INVALID_EOF_STATE;
            return 0;
        }

        helper_parse_headers( &pNext, pParser, pSettings );
        helper_parse_headers_finish( &pNext, pParser, pSettings, &isHeadResponse );
        helper_parse_body( &pNext, pParser, pSettings, isHeadResponse, pData, len );
        pSettings->on_message_complete( pParser );
    }

    httpParserExecuteCallCount++;
    return len;
}

/* Mocked http_parser_execute callback that will be called the first time on the
 * response message up to the middle of the first header value, then the second
 * time on the response message from the middle of the first header value to the
 * end. */
static size_t http_parser_execute_partial_header_value( http_parser * pParser,
                                                        const http_parser_settings * pSettings,
                                                        const char * pData,
                                                        size_t len,
                                                        int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    const char * pNext = pData;
    uint8_t isHeadResponse = 0;
    const char * pHeaderFieldStart = NULL;
    size_t headerFieldLen = 0;
    const char * pHeaderValueStart = NULL;
    size_t headerValueLen = 0;

    if( httpParserExecuteCallCount == 0 )
    {
        pSettings->on_message_begin( pParser );

        helper_parse_status_line( &pNext, pParser, pSettings );

        /* Get the first header field. */
        pHeaderFieldStart = pNext;
        pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
        headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
        pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

        pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

        /* pNext now points to the start of the partial header value. */
        pHeaderValueStart = pNext;
        headerValueLen = len - ( size_t ) ( pHeaderValueStart - pData );
        pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );
    }
    else
    {
        /* In this second call to http_parser_execute mock, pData now starts
         * at the partial header value. */
        pHeaderValueStart = pNext;
        pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
        headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
        pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

        pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

        helper_parse_headers( &pNext, pParser, pSettings );
        helper_parse_headers_finish( &pNext, pParser, pSettings, &isHeadResponse );
        helper_parse_body( &pNext, pParser, pSettings, isHeadResponse, pData, len );

        pSettings->on_message_complete( pParser );
    }

    httpParserExecuteCallCount++;
    return len;
}

/* Mocked http_parser_execute callback that will be called the first time on the
 * response message up to the middle of the body, then the second time on the
 * response message from the middle of the body to the end. */
static size_t http_parser_execute_partial_body( http_parser * pParser,
                                                const http_parser_settings * pSettings,
                                                const char * pData,
                                                size_t len,
                                                int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    const char * pNext = pData;

    if( httpParserExecuteCallCount == 0 )
    {
        pSettings->on_message_begin( pParser );

        helper_parse_status_line( &pNext, pParser, pSettings );
        helper_parse_headers( &pNext, pParser, pSettings );
        helper_parse_headers_finish( &pNext, pParser, pSettings, NULL );
        helper_parse_body( &pNext, pParser, pSettings, 0, pData, len );
    }
    else
    {
        /* Parse the rest of the body. */
        helper_parse_body( &pNext, pParser, pSettings, 0, pData, len );

        pSettings->on_message_complete( pParser );
    }

    httpParserExecuteCallCount++;
    return len;
}

/* Mocked http_parser_execute callback that will be on a response of type
 * transfer-encoding chunked. */
static size_t http_parser_execute_chunked_body( http_parser * pParser,
                                                const http_parser_settings * pSettings,
                                                const char * pData,
                                                size_t len,
                                                int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    const char * pNext = pData;
    uint8_t isHeadResponse = 0;
    const char * pBody = NULL;
    size_t bodyLen = 0;
    const char * pChunkHeader = NULL;

    pSettings->on_message_begin( pParser );

    helper_parse_status_line( &pNext, pParser, pSettings );
    helper_parse_headers( &pNext, pParser, pSettings );
    helper_parse_headers_finish( &pNext, pParser, pSettings, &isHeadResponse );

    /* pNext now points to the start of the first chunk header. Loop until the
     * last chunk header is detected. A "\r\" follows the last chunk header
     * (length 0 chunk header). */
    while( *pNext != '\r' )
    {
        pChunkHeader = pNext;
        bodyLen = ( size_t ) strtoul( pChunkHeader, NULL, 16 );

        pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
        pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

        pBody = pNext;

        if( bodyLen > 0 )
        {
            pSettings->on_body( pParser, pBody, bodyLen );
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
        }
    }

    pSettings->on_message_complete( pParser );

    httpParserExecuteCallCount++;
    return len;
}

/* ============================ UNITY FIXTURES ============================== */

/* Called before each test case. */
void setUp( void )
{
    /* Setup global testing variables. */
    hasConnectionClose = 0;
    hasConnectionKeepAlive = 0;
    contentLength = ULLONG_MAX;
    headerCallbackCount = 0;
    sendCurrentCall = 0;
    sendErrorCall = 0;
    sendPartialCall = 0;
    checkContentLength = 0;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_HEAD;
    networkDataLen = HTTP_TEST_RESPONSE_HEAD_LENGTH;
    firstPartBytes = networkDataLen;
    recvCurrentCall = 0;
    recvStopCall = UINT8_MAX;
    httpParserExecuteCallCount = 0;
    httpParsingErrno = HPE_OK;
    transportInterface.recv = transportRecvSuccess;
    transportInterface.send = transportSendSuccess;
    transportInterface.pContext = NULL;
    requestHeaders.pBuffer = httpBuffer;
    requestHeaders.bufferLen = sizeof( httpBuffer );
    memcpy( requestHeaders.pBuffer, HTTP_TEST_REQUEST_HEAD_HEADERS, HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH;
    memset( &response, 0, sizeof( HTTPResponse_t ) );
    headerParsingCallback.onHeaderCallback = onHeaderCallback;
    headerParsingCallback.pContext = NULL;
    response.pBuffer = httpBuffer;
    response.bufferLen = sizeof( httpBuffer );
    response.pHeaderParsingCallback = &headerParsingCallback;

    /* Ignore third-party init functions that return void. */
    http_parser_init_Ignore();
    http_parser_settings_init_Ignore();
    http_parser_set_max_header_size_Ignore();
    http_errno_description_IgnoreAndReturn( "Dummy unit test print." );
}

/* ======================== Testing HTTPClient_Send ========================= */

/* Test successfully parsing a response to a HEAD request. The full response
 * message is present in the response buffer on the first network read. */
void test_HTTPClient_Send_HEAD_request_parse_whole_response( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_whole_response );

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0U, response.bodyLen );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ), response.headersLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test successfully parsing a response to a PUT request. The full response
 * message is present in the response buffer on the first network read. */
void test_HTTPClient_Send_PUT_request_parse_whole_response( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_whole_response );

    checkContentLength = 1;
    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_PUT_HEADERS,
            HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_PUT;
    networkDataLen = HTTP_TEST_RESPONSE_PUT_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_PUT_LENGTH;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_PUT_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.headersLen );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( 0, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_PUT_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test successfully parsing a response to a GET request. The full response
 * message is present in the response buffer on the first network read. */
void test_HTTPClient_Send_GET_request_parse_whole_response( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_whole_response );

    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_GET_HEADERS,
            HTTP_TEST_REQUEST_GET_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_GET;
    networkDataLen = HTTP_TEST_RESPONSE_GET_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_GET_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH, response.headersLen );
    TEST_ASSERT_EQUAL( response.pHeaders + HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH, response.pBody );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_BODY_LENGTH, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_CONTENT_LENGTH, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test successfully parsing a response where there are no headers. The full
 * response message is present in the response buffer on the first network read. */
void test_HTTPClient_Send_no_response_headers( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_whole_response );

    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_NO_HEADERS;
    networkDataLen = HTTP_TEST_RESPONSE_NO_HEADERS_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_NO_HEADERS_LENGTH;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0U, response.bodyLen );
    TEST_ASSERT_EQUAL( NULL, response.pHeaders );
    TEST_ASSERT_EQUAL( 0, response.headersLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( 0, response.contentLength );
    TEST_ASSERT_EQUAL( 0, response.headerCount );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test successfully parsing a response where up to the middle of a header field
 * is received on the first network read, then the rest of the response on the
 * second read. */
void test_HTTPClient_Send_parse_partial_header_field( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_partial_header_field );

    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_FIELD_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0, response.bodyLen );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ), response.headersLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test successfully parsing a response where up to the middle of a header value
 * is received on the first network read, then the rest of the response on the
 * second read. */
void test_HTTPClient_Send_parse_partial_header_value( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_partial_header_value );

    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0, response.bodyLen );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ), response.headersLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test successfully parsing a response where up to the middle of the body
 * is received on the first network read, then the rest of the response on the
 * second read. */
void test_HTTPClient_Send_parse_partial_body( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_partial_body );

    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_GET_HEADERS,
            HTTP_TEST_REQUEST_GET_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_GET;
    networkDataLen = HTTP_TEST_RESPONSE_GET_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_GET_PARTIAL_BODY_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH, response.headersLen );
    TEST_ASSERT_EQUAL( response.pHeaders + HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH, response.pBody );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_BODY_LENGTH, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_CONTENT_LENGTH, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_GET_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test receiving a response where the body is of Transfer-Encoding chunked. */
void test_HTTPClient_Send_parse_chunked_body( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_chunked_body );

    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_PUT_HEADERS,
            HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_CHUNKED;
    networkDataLen = HTTP_TEST_RESPONSE_CHUNKED_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_CHUNKED_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_CHUNKED_HEADERS_LENGTH, response.headersLen );
    TEST_ASSERT_EQUAL( ( response.pHeaders + response.headersLen ), response.pBody );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_CHUNKED_BODY_LENGTH, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( 0, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_CHUNKED_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test a timeout is returned from the first network read. */
void test_HTTPClient_Send_timeout_recv_immediate( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_ExpectAnyArgsAndReturn( 0 );

    recvStopCall = 0;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_NO_RESPONSE, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a timeout is received from the second network read. In the first
 * network read a partial response is received and parsed. */
void test_HTTPClient_Send_timeout_partial_response( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_partial_header_field );
    http_errno_description_IgnoreAndReturn( "Dummy unit test print." );

    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH;
    recvStopCall = 1;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_PARTIAL_RESPONSE, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test the buffer limit is reached on the network read, but the parser indicated
 * the response is not complete. */
void test_HTTPClient_Send_response_larger_than_buffer( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_partial_body );
    http_errno_description_IgnoreAndReturn( "Dummy unit test print." );

    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_GET_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_GET;
    networkDataLen = HTTP_TEST_RESPONSE_GET_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_GET_PARTIAL_BODY_LENGTH;
    response.bufferLen = HTTP_TEST_RESPONSE_GET_PARTIAL_BODY_LENGTH;

    /* For everage of no header parsing callback configured. */
    response.pHeaderParsingCallback = NULL;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_INSUFFICIENT_MEMORY, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test sending a request with a NULL response configured. */
void test_HTTPClient_Send_null_response( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_PUT_HEADERS,
            HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    NULL,
                                    0U );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a network error is returned when sending the request headers. */
void test_HTTPClient_Send_network_error_request_headers( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    sendErrorCall = 0U;
    transportInterface.send = transportSendNetworkError;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0U,
                                    &response,
                                    0U );
    TEST_ASSERT_EQUAL( HTTP_NETWORK_ERROR, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a network error is returned when sending the request body. */
void test_HTTPClient_Send_network_error_request_body( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    transportInterface.send = transportSendNetworkError;

    /* There is no Content-Length header written so the call to send an error on
     * is call 1. */
    sendErrorCall = 1U;
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response,
                                    HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG );

    TEST_ASSERT_EQUAL( HTTP_NETWORK_ERROR, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test less bytes, of the request headers, are sent than expected. */
void test_HTTPClient_Send_less_bytes_request_headers( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_whole_response );

    transportInterface.send = transportSendLessThanBytesToWrite;
    sendPartialCall = 0U;
    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_PUT_HEADERS,
            HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_PUT;
    networkDataLen = HTTP_TEST_RESPONSE_PUT_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_PUT_LENGTH;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_PUT_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.headersLen );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( 0, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_PUT_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test less bytes, of the request body, are sent that expected. */
void test_HTTPClient_Send_less_bytes_request_body( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_execute_Stub( http_parser_execute_whole_response );

    transportInterface.send = transportSendLessThanBytesToWrite;

    sendPartialCall = 1U;
    memcpy( requestHeaders.pBuffer,
            HTTP_TEST_REQUEST_PUT_HEADERS,
            HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH );
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_PUT;
    networkDataLen = HTTP_TEST_RESPONSE_PUT_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_PUT_LENGTH;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response,
                                    HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG );

    TEST_ASSERT_EQUAL( HTTP_SUCCESS, returnStatus );
    TEST_ASSERT_EQUAL( response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.pHeaders );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_PUT_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ), response.headersLen );
    TEST_ASSERT_EQUAL( NULL, response.pBody );
    TEST_ASSERT_EQUAL( 0, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_STATUS_CODE_OK, response.statusCode );
    TEST_ASSERT_EQUAL( 0, response.contentLength );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_PUT_HEADER_COUNT, response.headerCount );
    TEST_ASSERT_BITS_LOW( HTTP_RESPONSE_CONNECTION_CLOSE_FLAG, response.respFlags );
    TEST_ASSERT_BITS_HIGH( HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG, response.respFlags );
}

/*-----------------------------------------------------------*/

/* Test when a network error is returned when receiving the response. */
void test_HTTPClient_Send_network_error_response( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_init_Ignore();

    transportInterface.recv = transportRecvNetworkError;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_NETWORK_ERROR, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test when more bytes are received than expected, when receiving a response
 * from the network. */
void test_HTTPClient_Send_recv_too_many_bytes( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_init_Ignore();

    transportInterface.recv = transportRecvMoreThanBytesToRead;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_NETWORK_ERROR, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test when more bytes are sent than expected, when sending data
 * over the socket. */
void test_HTTPClient_Send_send_too_many_bytes( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_init_Ignore();

    transportInterface.send = transportSendMoreThanBytesToWrite;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_NETWORK_ERROR, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a NULL transport interface passed to the API. */
void test_HTTPClient_Send_null_transport_interface( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    returnStatus = HTTPClient_Send( NULL,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a NULL transport send callback passed to the API. */
void test_HTTPClient_Send_null_transport_send( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    transportInterface.send = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a NULL transport receive callback passed to the API. */
void test_HTTPClient_Send_null_transport_recv( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    transportInterface.recv = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a NULL request headers structure passed to the API. */
void test_HTTPClient_Send_null_request_headers( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    NULL,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a null request headers buffer passed to the API. */
void test_HTTPClient_Send_null_request_header_buffer( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    requestHeaders.pBuffer = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a NULL response buffer passed to the API. */
void test_HTTPClient_Send_null_response_buffer( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    response.pBuffer = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test the request headers not containing enough bytes for a valid status-line.
 */
void test_HTTPClient_Send_not_enough_request_headers( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    requestHeaders.headersLen = HTTP_MINIMUM_REQUEST_LINE_LENGTH - 1;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test a NULL request body but a non-zero requets body length.
 */
void test_HTTPClient_Send_null_request_body_nonzero_body_length( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    1,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test when the Content-Length header cannot fit into the header buffer. */
void test_HTTPClient_Send_Content_Length_Header_Doesnt_Fit( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    requestHeaders.pBuffer = ( uint8_t * ) HTTP_TEST_REQUEST_PUT_HEADERS;

    /* Set the length of the buffer to be the same length as the current
     * amount of headers without the Content-Length. */
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response,
                                    0 );

    TEST_ASSERT_EQUAL( HTTP_INSUFFICIENT_MEMORY, returnStatus );
}

/*-----------------------------------------------------------*/

/* Test parsing errors are translated to the appropriate HTTP Client library
 * errors. */
void test_HTTPClient_Send_parsing_errors( void )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    http_parser_init_Ignore();
    http_parser_settings_init_Ignore();
    http_parser_execute_Stub( http_parser_execute_error );
    http_errno_description_IgnoreAndReturn( "Dummy unit test print." );

    httpParsingErrno = HPE_HEADER_OVERFLOW;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED, returnStatus );

    httpParsingErrno = HPE_INVALID_CHUNK_SIZE;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CHUNK_HEADER, returnStatus );

    httpParsingErrno = HPE_CLOSED_CONNECTION;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA, returnStatus );

    httpParsingErrno = HPE_INVALID_VERSION;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_PROTOCOL_VERSION, returnStatus );

    httpParsingErrno = HPE_INVALID_STATUS;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_STATUS_CODE, returnStatus );

    httpParsingErrno = HPE_STRICT;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CHARACTER, returnStatus );

    httpParsingErrno = HPE_INVALID_CONSTANT;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CHARACTER, returnStatus );

    httpParsingErrno = HPE_LF_EXPECTED;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CHARACTER, returnStatus );

    httpParsingErrno = HPE_INVALID_HEADER_TOKEN;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CHARACTER, returnStatus );

    httpParsingErrno = HPE_INVALID_CONTENT_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH, returnStatus );

    httpParsingErrno = HPE_UNEXPECTED_CONTENT_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH, returnStatus );

    httpParsingErrno = HPE_UNKNOWN;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response,
                                    0 );
    TEST_ASSERT_EQUAL( HTTP_PARSER_INTERNAL_ERROR, returnStatus );
}
