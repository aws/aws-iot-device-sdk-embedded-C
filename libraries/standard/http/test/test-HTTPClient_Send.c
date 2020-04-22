#include <string.h>
#include <stdio.h>
#include "common.h"


/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_sendHttpHeaders.c"
#include "_sendHttpBody.c"
#include "_receiveHttpResponse.c"
#include "HTTPClient_Send.c"


/* Template HTTP successful response with no body. */
#define HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY           \
    "HTTP/1.1 200 OK\r\n"                                  \
    "Content-Length: 43\r\n"                               \
    "Date: Sun, 14 Jul 2019 06:07:52 GMT\r\n"              \
    "ETag: \"3356-5233\"\r\n"                              \
    "Vary: *\r\n"                                          \
    "P3P: CP=\"This is not a P3P policy\"\r\n"             \
    "xserver: www1021\r\n\r\n"
#define HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY_LENGTH sizeof( HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY ) - 1

/* Template HTTP request for a head request. */
#define HTTP_TEST_REQUEST_HEAD                            \
    "HEAD /somedir/somepage.html HTTP/1.1\r\n"            \
    "test-header0: test-value0\r\n"                       \
    "test-header1: test-value1\r\n"                       \
    "test-header2: test-value2\r\n"                       \
    "test-header3: test-value0\r\n"                       \
    "test-header4: test-value1\r\n"                       \
    "test-header5: test-value2\r\n"                       \
    "\r\n"
#define HTTP_TEST_REQUEST_HEAD_LENGTH sizeof( HTTP_TEST_REQUEST_HEAD ) - 1

/* Test buffer to share among the test. */
static uint8_t httpBuffer[ 1024 ] = { 0 };

/* Mocked successful transport send. */
static int32_t transportSendSuccess( HTTPNetworkContext_t* pContext, 
                                     const void * pBuffer, 
                                     size_t bytesToWrite )
{
    ( void )pContext;
    ( void )pBuffer;
    return bytesToWrite;
}

/* Mocked successful transport read. */
static int32_t transportRecvSuccess( HTTPNetworkContext_t *pContext,
                                     void * pBuffer, 
                                     size_t bytesToRead )
{
    ( void )pContext;
    ( void )pBuffer;

    memcpy( pBuffer, 
            HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY, 
            sizeof( HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY ) - 1 );

    return sizeof( HTTP_TEST_RESPONSE_HEADER_LINES_NO_BODY ) - 1;
}

/* Mocked network error returning transport send. */
static int32_t transportSendNetworkError( HTTPNetworkContext_t* pContext, 
                                          const void * pBuffer, 
                                          size_t bytesToWrite )
{
    ( void )pContext;
    ( void )pBuffer;
    ( void )bytesToWrite;

    return -1;
}

/* Mocked transport send that returns less bytes than expected. */
static int32_t transportSendLessThanBytesToWrite( HTTPNetworkContext_t* pContext, 
                                                  const void * pBuffer, 
                                                  size_t bytesToWrite )
{
    ( void )pContext;
    ( void )pBuffer;
    ( void )bytesToWrite;

    return bytesToWrite - 1;
}


int main()
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    HTTPResponse_t response = { 0 };
    response.pBuffer = httpBuffer;
    response.bufferLen = sizeof( httpBuffer );

    HTTPTransportInterface_t transportInterface = 
    {
        .recv = transportRecvSuccess,
        .send = transportSendSuccess,
        .pContext = NULL
    };

    HTTPRequestHeaders_t requestHeadersHead = 
    {
        .pBuffer = ( uint8_t* )( HTTP_TEST_REQUEST_HEAD ),
        .bufferLen = sizeof( HTTP_TEST_REQUEST_HEAD ) - 1,
        .headersLen = sizeof( HTTP_TEST_REQUEST_HEAD ) - 1
    };

    #define reset() do {                                \
        transportInterface.recv = transportRecvSuccess; \
        transportInterface.send = transportSendSuccess; \
        transportInterface.pContext = NULL;             \
        requestHeadersHead.pBuffer = ( uint8_t* )( HTTP_TEST_REQUEST_HEAD );  \
        requestHeadersHead.bufferLen = sizeof( HTTP_TEST_REQUEST_HEAD ) - 1;  \
        requestHeadersHead.headersLen = sizeof( HTTP_TEST_REQUEST_HEAD ) - 1; \
    } while( 0 )
    reset();

    /* -----------------------------------------------------------------------*/

    /* Happy Path testing. Test sending a request and successfully receiving a
     * response that is within the bounds of the response buffer. */
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_SUCCESS );
    /* TODO: Check the response is parsed successfully. */
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test an error returned from a unsuccessful transport send. */
    transportInterface.send = transportSendNetworkError;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test less bytes than expected returned from transport send. */
    transportInterface.send = transportSendLessThanBytesToWrite;

    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_NETWORK_ERROR );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface. */
    returnStatus = HTTPClient_Send( NULL,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();


    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface. */
    returnStatus = HTTPClient_Send( NULL,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface. */
    returnStatus = HTTPClient_Send( NULL,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface send. */
    transportInterface.send = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL transport interface recv. */
    transportInterface.recv = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeadersHead,
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
    requestHeadersHead.pBuffer = NULL;
    returnStatus = HTTPClient_Send( &transportInterface,
                                    &requestHeadersHead,
                                    NULL,
                                    0,
                                    &response );

    ok( returnStatus == HTTP_INVALID_PARAMETER );
    reset();

    return grade();
}