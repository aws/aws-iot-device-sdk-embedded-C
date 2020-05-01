#include <string.h>
#include <stdio.h>
#include "common.h"

/* THESE TESTS WILL MOVE TO THE UNITY FRAMEWORK.
 * ok()'s will be replaced with proper unity macros. */

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
#define HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH    sizeof( HTTP_TEST_REQUEST_HEAD_HEADERS ) - 1

/* Template HTTP request for a PUT request. */
#define HTTP_TEST_REQUEST_PUT_HEADERS         \
    "PUT /somedir/somepage.html HTTP/1.1\r\n" \
    "Content-Length: 26\r\n"                  \
    "test-header1: test-value1\r\n"           \
    "test-header2: test-value2\r\n"           \
    "test-header3: test-value0\r\n"           \
    "test-header4: test-value1\r\n"           \
    "test-header5: test-value2\r\n"           \
    "\r\n"
#define HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH    sizeof( HTTP_TEST_REQUEST_PUT_HEADERS ) - 1
#define HTTP_TEST_REQUEST_PUT_BODY              "abcdefghijklmnopqrstuvwxyz"
#define HTTP_TEST_REQUEST_PUT_BODY_LENGTH       sizeof( HTTP_TEST_REQUEST_PUT_BODY ) - 1

/* Template HTTP request for a GET request. */
#define HTTP_TEST_REQUEST_GET_HEADERS         \
    "GET /somedir/somepage.html HTTP/1.1\r\n" \
    "test-header1: test-value1\r\n"           \
    "test-header2: test-value2\r\n"           \
    "test-header3: test-value0\r\n"           \
    "test-header4: test-value1\r\n"           \
    "test-header5: test-value2\r\n"           \
    "\r\n"
#define HTTP_TEST_REQUEST_GET_HEADERS_LENGTH               sizeof( HTTP_TEST_REQUEST_GET_HEADERS ) - 1

/* HTTP OK Status-Line. */
#define HTTP_STATUS_LINE_OK                                "HTTP/1.1 200 OK\r\n"
#define HTTP_STATUS_CODE_OK                                200

#define HTTP_TEST_CONTENT_LENGTH_HEADER_LINE               "Content-Length: 43\r\n"
#define HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_FIELD      "Content-Len"
#define HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_VALUE      "Content-Length: 4"
#define HTTP_TEST_DATE_HEADER_LINE                         "Date: Sun, 14 Jul 2019 06:07:52 GMT\r\n"
#define HTTP_TEST_ETAG_HEADER_LINE                         "ETag: \"3356-5233\"\r\n"
#define HTTP_TEST_VARY_HEADER_LINE                         "Vary: *\r\n"
#define HTTP_TEST_P3P_HEADER_LINE                          "P3P: CP=\"This is not a P3P policy\"\r\n"
#define HTTP_TEST_XSERVER_HEADER_LINE                      "xserver: www1021\r\n"
#define HTTP_TEST_CONNECTION_CLOSE_HEADER_LINE             "Connection: close\r\n"
#define HTTP_TEST_CONNECTION_KEEP_ALIVE_HEADER_LINE        "Connection: keep-alive\r\n"
#define HTTP_TEST_TRANSFER_ENCODING_CHUNKED_HEADER_LINE    "Transfer-Encoding: chunked\r\n"

/* Template HTTP successful response with no body. This is for a HEAD request. */
#define HTTP_TEST_RESPONSE_HEAD            \
    HTTP_STATUS_LINE_OK                    \
    HTTP_TEST_CONTENT_LENGTH_HEADER_LINE   \
    HTTP_TEST_CONNECTION_CLOSE_HEADER_LINE \
    HTTP_TEST_DATE_HEADER_LINE             \
    HTTP_TEST_ETAG_HEADER_LINE             \
    HTTP_TEST_VARY_HEADER_LINE             \
    HTTP_TEST_P3P_HEADER_LINE              \
    HTTP_TEST_XSERVER_HEADER_LINE HTTP_HEADER_LINE_SEPARATOR
#define HTTP_TEST_RESPONSE_HEAD_LENGTH                         sizeof( HTTP_TEST_RESPONSE_HEAD ) - 1U
#define HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT                   7
#define HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH                 43
#define HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_FIELD_LENGTH    sizeof( HTTP_STATUS_LINE_OK ) + sizeof( HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_FIELD ) - 2U
#define HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH    sizeof( HTTP_STATUS_LINE_OK ) + sizeof( HTTP_TEST_CONTENT_LENGTH_PARTIAL_HEADER_VALUE ) - 2U

/* Template HTTP successful response with no body. */
#define HTTP_TEST_RESPONSE_PUT                  \
    HTTP_STATUS_LINE_OK                         \
    HTTP_TEST_CONNECTION_KEEP_ALIVE_HEADER_LINE \
    HTTP_TEST_DATE_HEADER_LINE                  \
    HTTP_TEST_ETAG_HEADER_LINE                  \
    HTTP_TEST_VARY_HEADER_LINE                  \
    HTTP_TEST_P3P_HEADER_LINE                   \
    HTTP_TEST_XSERVER_HEADER_LINE HTTP_HEADER_LINE_SEPARATOR
#define HTTP_TEST_RESPONSE_PUT_LENGTH          sizeof( HTTP_TEST_RESPONSE_PUT ) - 1U
#define HTTP_TEST_RESPONSE_PUT_HEADER_COUNT    6

/* Template HTTP successful response with body. */
#define HTTP_TEST_RESPONSE_GET \
    HTTP_TEST_RESPONSE_HEAD    \
    "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopq"
#define HTTP_TEST_RESPONSE_GET_LENGTH                 sizeof( HTTP_TEST_RESPONSE_GET ) - 1U
#define HTTP_TEST_RESPONSE_GET_HEADER_COUNT           HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT
#define HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH         HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U )
#define HTTP_TEST_RESPONSE_GET_BODY_LENGTH            HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH
#define HTTP_TEST_RESPONSE_GET_CONTENT_LENGTH         HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH
#define HTTP_TEST_RESPONSE_GET_PARTIAL_BODY_LENGTH    HTTP_TEST_RESPONSE_GET_LENGTH - 13U

/* Template HTTP successful response with no body. */
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
#define HTTP_TEST_RESPONSE_CHUNKED_LENGTH          sizeof( HTTP_TEST_RESPONSE_CHUNKED ) - 1U
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

/* Test buffer to share among the test. */
#define HTTP_TEST_BUFFER_LENGTH    1024
static uint8_t httpBuffer[ HTTP_TEST_BUFFER_LENGTH ] = { 0 };

/* -----------------------------------------------------------------------*/

/* Each test will update these variables in the headerCallbackCount. */
uint8_t hasConnectionClose;
uint8_t hasConnectionKeepAlive;
size_t contentLength;

/* -----------------------------------------------------------------------*/

uint8_t headerCallbackCount;
/* HTTP header callback. */
static void onHeaderCallback( void * pContext,
                              const uint8_t * fieldLoc,
                              size_t fieldLen,
                              const uint8_t * valueLoc,
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
#define headerCallbackReset()       \
    do {                            \
        headerCallbackCount = 0;    \
        hasConnectionClose = 0;     \
        hasConnectionKeepAlive = 0; \
        contentLength = 0;          \
    }                               \
    while( 0 )

/* -----------------------------------------------------------------------*/

#define CARRIAGE_RETURN_CHARACTER    "\r"

/* We don't want to write a whole new parser, so the mocked behavior should
 * simply invoke the callbacks for the test cases of interest. */
enum parsingUnitTestTypes
{
    PARSE_WHOLE_RESPONSE,
    PARTIAL_HEADER_FIELD,
    PARTIAL_HEADER_VALUE,
    PARTIAL_BODY,
    CHUNKED_BODY
};

enum http_errno httpParsingErrno;
enum parsingUnitTestTypes parsingTestType;
uint8_t httpParserExecuteCallCount;
size_t http_parser_execute( http_parser * pParser,
                            const http_parser_settings * pSettings,
                            const char * data,
                            size_t len )
{
    /* Pointer to the next place in the response to parse. */
    const char * pNext = data;
    uint8_t isHeadResponse = 0;

    /* Error case mocking. */
    if( httpParsingErrno != HPE_OK )
    {
        pParser->http_errno = httpParsingErrno;
        return 0;
    }

    /* If no data is received when parsing has not even started, then there is
     * no parsing error. */
    if( ( len == 0 ) && ( httpParserExecuteCallCount == 0 ) )
    {
        return 0;
    }

    /* In this test type the mocked function is input a whole complete response. */
    /* With CMOCK we can move these test types to different function for mocking callback. */
    if( parsingTestType == PARSE_WHOLE_RESPONSE )
    {
        pSettings->on_message_begin( pParser );

        /* For purposes of unit testing the response is well formed in the non-error
         * cases, so the reason-phrase is always after HTTP/1.1 and the three digit
         * status code. strstr() is used only for unit testing where test input are \
         * always string literals. strstr() should not be used in application code. */
        pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the status-code. */
        pNext += SPACE_CHARACTER_LEN;
        pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the reason-phrase. */
        pNext += SPACE_CHARACTER_LEN;
        const char * pReasonPhraseStart = pNext;
        pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
        pParser->status_code = 200;
        pSettings->on_status( pParser,
                              pReasonPhraseStart,
                              ( size_t ) ( pNext - pReasonPhraseStart ) );

        pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

        while( *pNext != '\r' )
        {
            const char * pHeaderFieldStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
            size_t headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
            pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

            pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

            const char * pHeaderValueStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            size_t headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
            pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
        }

        pParser->content_length = contentLength;

        if( hasConnectionClose )
        {
            pParser->flags |= F_CONNECTION_CLOSE;
        }

        if( hasConnectionKeepAlive )
        {
            pParser->flags |= F_CONNECTION_KEEP_ALIVE;
        }

        isHeadResponse = pSettings->on_headers_complete( pParser );
        pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
        const char * pBody = pNext;

        if( isHeadResponse == 0 )
        {
            size_t bodyLen = ( size_t ) ( len - ( size_t ) ( pBody - data ) );

            if( bodyLen > 0 )
            {
                pSettings->on_body( pParser, pBody, bodyLen );
            }
        }

        pSettings->on_message_complete( pParser );
    }

    if( parsingTestType == PARTIAL_HEADER_FIELD )
    {
        if( httpParserExecuteCallCount == 0 )
        {
            pSettings->on_message_begin( pParser );
            pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the status-code. */
            pNext += SPACE_CHARACTER_LEN;
            pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the reason-phrase. */
            pNext += SPACE_CHARACTER_LEN;
            const char * pReasonPhraseStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            pParser->status_code = 200;
            pSettings->on_status( pParser,
                                  pReasonPhraseStart,
                                  ( size_t ) ( pNext - pReasonPhraseStart ) );

            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            const char * pHeaderFieldStart = pNext;
            size_t headerFieldLen = len - ( size_t ) ( pHeaderFieldStart - data );
            pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );
        }
        else
        {
            if( len == 0 )
            {
                pParser->http_errno = HPE_INVALID_EOF_STATE;
                return 0;
            }

            while( *pNext != '\r' )
            {
                const char * pHeaderFieldStart = pNext;
                pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
                size_t headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
                pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

                pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

                const char * pHeaderValueStart = pNext;
                pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
                size_t headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
                pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

                pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            }

            pParser->content_length = contentLength;

            if( hasConnectionClose )
            {
                pParser->flags |= F_CONNECTION_CLOSE;
            }

            if( hasConnectionKeepAlive )
            {
                pParser->flags |= F_CONNECTION_KEEP_ALIVE;
            }

            isHeadResponse = pSettings->on_headers_complete( pParser );
            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            const char * pBody = pNext;

            if( isHeadResponse == 0 )
            {
                size_t bodyLen = ( size_t ) ( len - ( size_t ) ( pBody - data ) );

                if( bodyLen > 0 )
                {
                    pSettings->on_body( pParser, pBody, bodyLen );
                }
            }

            pSettings->on_message_complete( pParser );
        }
    }

    if( parsingTestType == PARTIAL_HEADER_VALUE )
    {
        if( httpParserExecuteCallCount == 0 )
        {
            pSettings->on_message_begin( pParser );

            /* For purposes of unit testing the response is well formed in the non-error
             * cases, so the reason-phrase is always after HTTP/1.1 and the three digit
             * status code. strstr() is used only for unit testing where test input are \
             * always string literals. strstr() should not be used in application code. */
            pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the status-code. */
            pNext += SPACE_CHARACTER_LEN;
            pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the reason-phrase. */
            pNext += SPACE_CHARACTER_LEN;
            const char * pReasonPhraseStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            pParser->status_code = 200;
            pSettings->on_status( pParser,
                                  pReasonPhraseStart,
                                  ( size_t ) ( pNext - pReasonPhraseStart ) );

            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

            const char * pHeaderFieldStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
            size_t headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
            pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

            pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

            const char * pHeaderValueStart = pNext;
            size_t headerValueLen = len - ( size_t ) ( pHeaderValueStart - data );
            pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );
        }
        else
        {
            if( len == 0 )
            {
                pParser->http_errno = HPE_INVALID_EOF_STATE;
                return 0;
            }

            if( len == 0 )
            {
                pParser->http_errno = HPE_INVALID_EOF_STATE;
                return 0;
            }

            const char * pHeaderValueStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            size_t headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
            pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

            pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

            while( *pNext != '\r' )
            {
                const char * pHeaderFieldStart = pNext;
                pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
                size_t headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
                pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

                pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

                pHeaderValueStart = pNext;
                pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
                headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
                pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

                pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            }

            pParser->content_length = contentLength;

            if( hasConnectionClose )
            {
                pParser->flags |= F_CONNECTION_CLOSE;
            }

            if( hasConnectionKeepAlive )
            {
                pParser->flags |= F_CONNECTION_KEEP_ALIVE;
            }

            isHeadResponse = pSettings->on_headers_complete( pParser );
            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            const char * pBody = pNext;

            if( isHeadResponse == 0 )
            {
                size_t bodyLen = ( size_t ) ( len - ( size_t ) ( pBody - data ) );

                if( bodyLen > 0 )
                {
                    pSettings->on_body( pParser, pBody, bodyLen );
                }
            }

            pSettings->on_message_complete( pParser );
        }
    }

    if( parsingTestType == PARTIAL_BODY )
    {
        if( httpParserExecuteCallCount == 0 )
        {
            pSettings->on_message_begin( pParser );

            /* For purposes of unit testing the response is well formed in the non-error
             * cases, so the reason-phrase is always after HTTP/1.1 and the three digit
             * status code. strstr() is used only for unit testing where test input are \
             * always string literals. strstr() should not be used in application code. */
            pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the status-code. */
            pNext += SPACE_CHARACTER_LEN;
            pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the reason-phrase. */
            pNext += SPACE_CHARACTER_LEN;
            const char * pReasonPhraseStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            pParser->status_code = 200;
            pSettings->on_status( pParser,
                                  pReasonPhraseStart,
                                  ( size_t ) ( pNext - pReasonPhraseStart ) );

            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

            while( *pNext != '\r' )
            {
                const char * pHeaderFieldStart = pNext;
                pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
                size_t headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
                pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

                pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

                const char * pHeaderValueStart = pNext;
                pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
                size_t headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
                pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

                pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            }

            pParser->content_length = contentLength;

            if( hasConnectionClose )
            {
                pParser->flags |= F_CONNECTION_CLOSE;
            }

            if( hasConnectionKeepAlive )
            {
                pParser->flags |= F_CONNECTION_KEEP_ALIVE;
            }

            isHeadResponse = pSettings->on_headers_complete( pParser );
            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

            const char * pBody = pNext;
            size_t bodyLen = ( size_t ) ( len - ( size_t ) ( pBody - data ) );

            if( bodyLen > 0 )
            {
                pSettings->on_body( pParser, pBody, bodyLen );
            }
        }
        else
        {
            const char * pBody = pNext;
            size_t bodyLen = ( size_t ) ( len - ( size_t ) ( pBody - data ) );

            if( bodyLen > 0 )
            {
                pSettings->on_body( pParser, pBody, bodyLen );
            }

            pSettings->on_message_complete( pParser );
        }
    }

    if( parsingTestType == CHUNKED_BODY )
    {
        pSettings->on_message_begin( pParser );

        pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the status-code. */
        pNext += SPACE_CHARACTER_LEN;
        pNext = strstr( pNext, SPACE_CHARACTER ); /* Get the space before the reason-phrase. */
        pNext += SPACE_CHARACTER_LEN;
        const char * pReasonPhraseStart = pNext;
        pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
        pParser->status_code = 200;
        pSettings->on_status( pParser,
                              pReasonPhraseStart,
                              ( size_t ) ( pNext - pReasonPhraseStart ) );

        pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

        while( *pNext != '\r' )
        {
            const char * pHeaderFieldStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_FIELD_SEPARATOR );
            size_t headerFieldLen = ( size_t ) ( pNext - pHeaderFieldStart );
            pSettings->on_header_field( pParser, pHeaderFieldStart, headerFieldLen );

            pNext += HTTP_HEADER_FIELD_SEPARATOR_LEN;

            const char * pHeaderValueStart = pNext;
            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            size_t headerValueLen = ( size_t ) ( pNext - pHeaderValueStart );
            pSettings->on_header_value( pParser, pHeaderValueStart, headerValueLen );

            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
        }

        pParser->content_length = contentLength;

        if( hasConnectionClose )
        {
            pParser->flags |= F_CONNECTION_CLOSE;
        }

        if( hasConnectionKeepAlive )
        {
            pParser->flags |= F_CONNECTION_KEEP_ALIVE;
        }

        isHeadResponse = pSettings->on_headers_complete( pParser );
        pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

        /* A "\r\" follows the last chunk header (length 0 chunk header). */
        while( *pNext != '\r' )
        {
            const char * pChunkHeader = pNext;
            size_t bodyLen = ( size_t ) strtoul( pChunkHeader, NULL, 16 );

            pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
            pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;

            const char * pBody = pNext;

            if( bodyLen > 0 )
            {
                pSettings->on_body( pParser, pBody, bodyLen );
                pNext = strstr( pNext, HTTP_HEADER_LINE_SEPARATOR );
                pNext += HTTP_HEADER_LINE_SEPARATOR_LEN;
            }
        }

        pSettings->on_message_complete( pParser );
    }

    httpParserExecuteCallCount++;
    return len;
}

#define hpeReset()                              \
    do {                                        \
        httpParsingErrno = HPE_OK;              \
        parsingTestType = PARSE_WHOLE_RESPONSE; \
        httpParserExecuteCallCount = 0;         \
    }                                           \
    while( 0 )


/* -----------------------------------------------------------------------*/

/* Mocked successful transport send. */
static int32_t transportSendSuccess( HTTPNetworkContext_t * pContext,
                                     const void * pBuffer,
                                     size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;
    return bytesToWrite;
}

/* -----------------------------------------------------------------------*/

/* This section  contains all the support needed to mock the two different
 * transport interface send cases. The three transport send error cases are:
 * 1. A negative value returned.
 * 2. Less than bytesToWrite returned. */

/* Transport send is called separately for the headers and the body, this counts
 * the number of calls so far. */
uint8_t sendCurrentCall;
uint8_t sendErrorCall;
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

static int32_t transportSendLessThanBytesToWrite( HTTPNetworkContext_t * pContext,
                                                  const void * pBuffer,
                                                  size_t bytesToWrite )
{
    ( void ) pContext;
    ( void ) pBuffer;
    int32_t retVal = bytesToWrite;

    if( sendErrorCall == sendCurrentCall )
    {
        retVal -= 1;
    }

    sendCurrentCall++;
    return retVal;
}

#define transportSendErrorReset() \
    do {                          \
        sendCurrentCall = 0;      \
        sendErrorCall = 0;        \
    }                             \
    while( 0 )

/* -----------------------------------------------------------------------*/


/* Testing an incremental transport receive receives in two parts. By defining
 * exactly which parts of the incremental receive, the mocked http_parser_execute()
 * does not need to look for partial headers and keep track of state. Keeping
 * track of state and looking for partial headers is essentially rewriting the
 * parser, which we do not want to do. */
uint8_t * pNetworkData;  /* The network data to read. */
size_t networkDataLen;   /* The network data to read's length. */
size_t firstPartBytes;   /* The number of bytes to send in the first part. */
uint8_t recvCurrentCall; /* The current number of calls. */
uint8_t recvStopCall;    /* Set this to when to return zero from this function. */
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

#define transportRecvReset()                             \
    do                                                   \
    {                                                    \
        pNetworkData = HTTP_TEST_RESPONSE_HEAD;          \
        networkDataLen = HTTP_TEST_RESPONSE_HEAD_LENGTH; \
        firstPartBytes = networkDataLen;                 \
        recvCurrentCall = 0;                             \
        recvStopCall = UINT8_MAX;                        \
    } while( 0 )

/* -----------------------------------------------------------------------*/

/* Mocked network error returning transport recv. */
static int32_t transportRecvNetworkError( HTTPNetworkContext_t * pContext,
                                          void * pBuffer,
                                          size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;
    ( void ) bytesToRead;

    return -1;
}

/* -----------------------------------------------------------------------*/

/* Mocked transport recv function that returns more bytes than expected. */
static int32_t transportRecvMoreThanBytesToRead( HTTPNetworkContext_t * pContext,
                                                 void * pBuffer,
                                                 size_t bytesToRead )
{
    ( void ) pContext;
    ( void ) pBuffer;

    return( bytesToRead + 1 );
}

/* -----------------------------------------------------------------------*/


/* Functions are pulled out into their own C files to be tested as a unit. */
#include "sendHttpHeaders.c"
#include "sendHttpBody.c"
#include "receiveHttpResponse.c"
#include "processCompleteHeader.c"
#include "httpParserOnMessageBeginCallback.c"
#include "httpParserOnStatusCallback.c"
#include "httpParserOnHeaderFieldCallback.c"
#include "httpParserOnHeaderValueCallback.c"
#include "httpParserOnHeadersCompleteCallback.c"
#include "httpParserOnMessageCompleteCallback.c"
#include "httpParserOnBodyCallback.c"
#include "initializeParsingContextForFirstResponse.c"
#include "processHttpParserError.c"
#include "parseHttpResponse.c"
#include "getFinalResponseStatus.c"
#include "receiveAndParseHttpResponse.c"
#include "HTTPClient_Send.c"

/* -----------------------------------------------------------------------*/

int main()
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    HTTPResponse_t response = { 0 };
    HTTPTransportInterface_t transportInterface = { 0 };
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPClient_HeaderParsingCallback_t headerParsingCallback = { 0 };

/* Resets each test back to the original happy path state. */
#define reset()                                                                    \
    do {                                                                           \
        transportRecvReset();                                                      \
        transportSendErrorReset();                                                 \
        headerCallbackReset();                                                     \
        hpeReset();                                                                \
        transportInterface.recv = transportRecvSuccess;                            \
        transportInterface.send = transportSendSuccess;                            \
        transportInterface.pContext = NULL;                                        \
        requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_HEAD_HEADERS ); \
        requestHeaders.bufferLen = HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH;          \
        requestHeaders.headersLen = HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH;         \
        memset( &response, 0, sizeof( HTTPResponse_t ) );                          \
        headerParsingCallback.onHeaderCallback = onHeaderCallback;                 \
        headerParsingCallback.pContext = NULL;                                     \
        response.pBuffer = httpBuffer;                                             \
        response.bufferLen = sizeof( httpBuffer );                                 \
        response.pHeaderParsingCallback = &headerParsingCallback;                  \
    }                                                                              \
    while( 0 )
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test sending a HEAD request and receiving the full response with both a
     * Content-Length and no body. */
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pBody == NULL );
    ok( response.bodyLen == 0 );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH );
    ok( response.headerCount == HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) != 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) == 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test sending a PUT request and receiving the full response with no
     * body. */
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    pNetworkData = HTTP_TEST_RESPONSE_PUT;
    networkDataLen = HTTP_TEST_RESPONSE_PUT_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_PUT_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_PUT_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) );
    ok( response.pBody == NULL );
    ok( response.bodyLen == 0 );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == 0 );
    ok( response.headerCount == HTTP_TEST_RESPONSE_PUT_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) == 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) != 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test sending a GET request and receiving the full response with no body. */
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_GET_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    pNetworkData = HTTP_TEST_RESPONSE_GET;
    networkDataLen = HTTP_TEST_RESPONSE_GET_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_GET_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH );
    ok( response.pBody == response.pHeaders + HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH );
    ok( response.bodyLen == HTTP_TEST_RESPONSE_GET_BODY_LENGTH );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == HTTP_TEST_RESPONSE_GET_CONTENT_LENGTH );
    ok( response.headerCount == HTTP_TEST_RESPONSE_GET_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) != 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) == 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test receiving the response message with part of the message received in
     * the middle of the header field. */
    parsingTestType = PARTIAL_HEADER_FIELD;
    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_FIELD_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pBody == NULL );
    ok( response.bodyLen == 0 );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH );
    ok( response.headerCount == HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) != 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) == 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test receiving the response message with part of the message received in
     * the middle of the header value. */
    parsingTestType = PARTIAL_HEADER_VALUE;
    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pBody == NULL );
    ok( response.bodyLen == 0 );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_HEAD_LENGTH - ( sizeof( HTTP_STATUS_LINE_OK ) - 1U ) );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == HTTP_TEST_RESPONSE_HEAD_CONTENT_LENGTH );
    ok( response.headerCount == HTTP_TEST_RESPONSE_HEAD_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) != 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) == 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test receiving the response message with part of the message received in
     * the middle of the HTTP body. */
    parsingTestType = PARTIAL_BODY;
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_GET_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_GET_HEADERS_LENGTH;
    pNetworkData = HTTP_TEST_RESPONSE_GET;
    networkDataLen = HTTP_TEST_RESPONSE_GET_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_GET_PARTIAL_BODY_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH );
    ok( response.pBody == response.pHeaders + HTTP_TEST_RESPONSE_GET_HEADERS_LENGTH );
    ok( response.bodyLen == HTTP_TEST_RESPONSE_GET_BODY_LENGTH );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == HTTP_TEST_RESPONSE_GET_CONTENT_LENGTH );
    ok( response.headerCount == HTTP_TEST_RESPONSE_GET_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) != 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) == 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test receiving a chunked body. */
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    parsingTestType = CHUNKED_BODY;
    pNetworkData = HTTP_TEST_RESPONSE_CHUNKED;
    networkDataLen = HTTP_TEST_RESPONSE_CHUNKED_LENGTH;
    firstPartBytes = HTTP_TEST_RESPONSE_CHUNKED_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    ok( response.pHeaders == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) );
    ok( response.headersLen == HTTP_TEST_RESPONSE_CHUNKED_HEADERS_LENGTH );
    ok( response.pBody == ( response.pHeaders + response.headersLen ) );
    ok( response.bodyLen == HTTP_TEST_RESPONSE_CHUNKED_BODY_LENGTH );
    ok( response.statusCode == HTTP_STATUS_CODE_OK );
    ok( response.contentLength == 0 );
    ok( response.headerCount == HTTP_TEST_RESPONSE_CHUNKED_HEADER_COUNT );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_CLOSE_FLAG ) == 0U );
    ok( ( response.flags & HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG ) != 0U );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test transport recv returning zero when first invoked. */
    recvStopCall = 0;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_NO_RESPONSE );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test transport recv returning zero in the middle of a response message. */
    /* This test will be invoked upon parsing implementation completion. */
    parsingTestType = PARTIAL_HEADER_VALUE;
    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH;
    recvStopCall = 1;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_PARTIAL_RESPONSE );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test the case where the response is larger than the buffer provided. */
    parsingTestType = PARTIAL_HEADER_VALUE;
    firstPartBytes = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH;
    response.bufferLen = HTTP_TEST_RESPONSE_HEAD_PARTIAL_HEADER_VALUE_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_INSUFFICIENT_MEMORY );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test receiving with a NULL response. */
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    NULL );
    ok( returnStatus == HTTP_SUCCESS );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a network error returned from a transport send of the request
     * headers. */
    sendErrorCall = 0;
    transportInterface.send = transportSendNetworkError;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a network error returned from a transport send of the request
     * body. */
    transportInterface.send = transportSendNetworkError;
    sendErrorCall = 1;
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response );

    ok( returnStatus == HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test less bytes than expected returned from a transport send of the
     * request headers. */
    transportInterface.send = transportSendLessThanBytesToWrite;
    sendErrorCall = 0U;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test less bytes than expected returned from a transport send of the
     * request body. */
    transportInterface.send = transportSendLessThanBytesToWrite;
    sendErrorCall = 1;
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response );

    ok( returnStatus == HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a network error returned from a transport recv of the response. */
    transportInterface.recv = transportRecvNetworkError;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus = HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test more bytes than expected returned from a transport recv of the
     * response. */
    transportInterface.recv = transportRecvMoreThanBytesToRead;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus = HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface. */
    returnStatus = HTTPClient_Send( NULL,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface send. */
    transportInterface.send = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface recv. */
    transportInterface.recv = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test NULL request headers structure. */
    returnStatus = HTTPClient_Send( &transportInterface,
                                    NULL,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test NULL request header buffer. */
    requestHeaders.pBuffer = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL response buffer. */
    response.pBuffer = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test the case where the length of the request headers is insufficient. */
    requestHeaders.headersLen = MINIMUM_REQUEST_LINE_LENGTH - 1;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_HEADER_OVERFLOW;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_INVALID_CHUNK_SIZE;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHUNK_HEADER );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_CLOSED_CONNECTION;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_INVALID_VERSION;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_PROTOCOL_VERSION );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_INVALID_STATUS;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_STATUS_CODE );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_STRICT;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_INVALID_CONSTANT;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_LF_EXPECTED;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_INVALID_HEADER_TOKEN;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_INVALID_CONTENT_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH );

    /* -----------------------------------------------------------------------*/

    /* Test each of the valid HTTP parsing errors. */
    httpParsingErrno = HPE_UNEXPECTED_CONTENT_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus == HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH );

    return grade();
}
