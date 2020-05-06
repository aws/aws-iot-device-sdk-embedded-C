#include <string.h>
#include <stdio.h>
#include "common.h"

/* THESE TESTS WILL MOVE TO THE UNITY FRAMEWORK.
 * ok()'s will be replaced with proper unity macros. */


/* Functions are pulled out into their own C files to be tested as a unit. */
#include "sendHttpHeaders.c"
#include "sendHttpBody.c"
#include "receiveHttpResponse.c"
#include "HTTPClient_InitializeParsingContext.c"
#include "HTTPClient_ParseResponse.c"
#include "getFinalResponseStatus.c"
#include "receiveAndParseHttpResponse.c"
#include "HTTPClient_Send.c"

/* HTTP OK Status-Line. */
#define HTTP_STATUS_LINE_OK    "HTTP/1.1 200 OK\r\n"
#define HTTP_STATUS_CODE_OK    200

/* Template HTTP successful response with no body. */
#define HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY \
    "HTTP/1.1 200 OK\r\n"                       \
    "Content-Length: 43\r\n"                    \
    "Date: Sun, 14 Jul 2019 06:07:52 GMT\r\n"   \
    "ETag: \"3356-5233\"\r\n"                   \
    "Vary: *\r\n"                               \
    "P3P: CP=\"This is not a P3P policy\"\r\n"  \
    "xserver: www1021\r\n\r\n"
#define HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_LENGTH          sizeof( HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY ) - 1U
#define HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_HEADER_COUNT    6


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

/* Test buffer to share among the test. */
#define HTTP_TEST_BUFFER_LENGTH                 1024
static uint8_t httpBuffer[ HTTP_TEST_BUFFER_LENGTH ] = { 0 };

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
    } while( 0 );

/* -----------------------------------------------------------------------*/

/* Mocked successful transport read. */
static int32_t transportRecvSuccess( HTTPNetworkContext_t * pContext,
                                     void * pBuffer,
                                     size_t bytesToRead )
{
    ( void ) pContext;

    memcpy( pBuffer,
            HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY,
            sizeof( HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY ) - 1 );

    return sizeof( HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY ) - 1;
}

/* -----------------------------------------------------------------------*/

/* This section contains all the support needed to mock an incremental transport
 * read. The mocked transport receive will read 128 bytes at time from the
 * response. */

/* Default increment read bytes transportRecvIncremental. */
#define INCREMENT_BYTES_DEFAULT    0x80U

uint32_t bytesRead;        /* Total bytes read over multple calls. */
uint8_t * pNetworkData;    /* The network data to read. */
size_t networkDataLen;     /* The network data to read's length. */
size_t incrementReadBytes; /* How many bytes of network data to read each call. */
size_t stopReadBytes;      /* Stop reading at >= this many bytes. */
static int32_t transportRecvIncremental( HTTPNetworkContext_t * pContext,
                                         void * pBuffer,
                                         size_t bytesToRead )
{
    ( void ) pContext;

    if( bytesRead >= stopReadBytes )
    {
        return 0;
    }

    uint8_t * pCopyLoc = pNetworkData + bytesRead;
    size_t messageLenLeft = networkDataLen - bytesRead;
    size_t copyLen = incrementReadBytes;

    /* If the amount requested to read is smaller than the increment, then
     * copy that amount. */
    if( bytesToRead < copyLen )
    {
        copyLen = bytesToRead;
    }

    /* If there is less message left than the amount to read, then copy the
     * rest. */
    if( messageLenLeft < copyLen )
    {
        copyLen = messageLenLeft;
    }

    memcpy( pBuffer, pCopyLoc, copyLen );
    bytesRead += copyLen;
    return copyLen;
}
#define transportRecvIncrementalReset()                                       \
    do {                                                                      \
        bytesRead = 0;                                                        \
        pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY; \
        networkDataLen = HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_LENGTH;      \
        incrementReadBytes = INCREMENT_BYTES_DEFAULT;                         \
        stopReadBytes = 0;                                                    \
    } while( 0 );


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

int main()
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    HTTPResponse_t response = { 0 };
    HTTPTransportInterface_t transportInterface = { 0 };
    HTTPRequestHeaders_t requestHeaders = { 0 };

/* Resets each test back to the original happy path state. */
#define reset()                                                                    \
    do {                                                                           \
        transportInterface.recv = transportRecvSuccess;                            \
        transportInterface.send = transportSendSuccess;                            \
        transportInterface.pContext = NULL;                                        \
        requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_HEAD_HEADERS ); \
        requestHeaders.bufferLen = HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH;          \
        requestHeaders.headersLen = HTTP_TEST_REQUEST_HEAD_HEADERS_LENGTH;         \
        memset( &response, 0, sizeof( HTTPResponse_t ) );                          \
        response.pBuffer = httpBuffer;                                             \
        response.bufferLen = sizeof( httpBuffer );                                 \
        transportRecvIncrementalReset();                                           \
        transportSendErrorReset();                                                 \
    } while( 0 );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Happy Path testing. Test sending a request and successfully receiving a
     * response that is within the bounds of the response buffer. */
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    /* Uncomment after parsing is implemented. */
    /* ok( response.body == NULL ); */
    /* ok( response.bodyLen == 0 ); */
    /* ok( response.headers == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) ); */
    /* ok( response.headersLen == HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_LENGTH ); */
    /* ok( response.statusCode == HTTP_STATUS_CODE_OK ); */
    /* ok( response.contentLength == 0 ); */
    /* ok( response.headerCount == HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_HEADER_COUNT ); */
    reset();

    /* -----------------------------------------------------------------------*/

    /* Happy path testing. Test sending a non-null body buffer and received a full
     * response. */
    requestHeaders.pBuffer = ( uint8_t * ) ( HTTP_TEST_REQUEST_PUT_HEADERS );
    requestHeaders.bufferLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    requestHeaders.headersLen = HTTP_TEST_REQUEST_PUT_HEADERS_LENGTH;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    ( uint8_t * ) HTTP_TEST_REQUEST_PUT_BODY,
                                    HTTP_TEST_REQUEST_PUT_BODY_LENGTH,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    /* Uncomment after parsing is implemented. */
    /* ok( response.body == NULL ); */
    /* ok( response.bodyLen == 0 ); */
    /* ok( response.headers == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) ); */
    /* ok( response.headersLen == HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_LENGTH ); */
    /* ok( response.statusCode == HTTP_STATUS_CODE_OK ); */
    /* ok( response.contentLength == 0 ); */
    /* ok( response.headerCount == HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_HEADER_COUNT ); */
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test receiving the response message with multiple calls to transport
     * recv. */
    transportInterface.recv = transportRecvIncremental;
    stopReadBytes = networkDataLen; /* Read the whole network data. */
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    /* Uncomment after parsing is implemented. */
    /* ok( response.body == NULL ); */
    /* ok( response.bodyLen == 0 ); */
    /* ok( response.headers == response.pBuffer + ( sizeof( HTTP_STATUS_LINE_OK ) - 1 ) ); */
    /* ok( response.headersLen == HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_LENGTH ); */
    /* ok( response.statusCode == HTTP_STATUS_CODE_OK ); */
    /* ok( response.contentLength == 0 ); */
    /* ok( response.headerCount == HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_HEADER_COUNT ); */
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

    /* Test transport recv returning zero when first invoked. */
    transportInterface.recv = transportRecvIncremental;
    stopReadBytes = 0; /* Stop immediately. */
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeaders,
                                    NULL,
                                    0,
                                    &response );
    ok( returnStatus = HTTP_NO_RESPONSE );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test transport recv returning zero in the middle of a response message. */
    /* This test will be invoked upon parsing implementation completion. */
    #if 0
        transportInterface.recv = transportRecvMoreThanBytesToRead;
        stopReadBytes = incrementReadBytes; /* Stop after the first increment. */
        returnStatus = HTTPClient_Send( &transportInterface,
                                        &requestHeaders,
                                        NULL,
                                        0,
                                        &response );
        ok( returnStatus = HTTP_PARTIAL_RESPONSE );
        reset();
    #endif

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

    return grade();
}
