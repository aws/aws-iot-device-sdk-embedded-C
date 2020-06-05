/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#ifndef DEMO_CONFIG_H_
#define DEMO_CONFIG_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging related header files are required to be included in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define LIBRARY_LOG_NAME and  LIBRARY_LOG_LEVEL.
 * 3. Include the header file "logging_stack.h".
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Demo. */
#define LIBRARY_LOG_NAME     "DEMO"
#define LIBRARY_LOG_LEVEL    LOG_INFO

#include "logging_stack.h"

/************ End of logging configuration ****************/

/**
 * @brief HTTP server host name.
 *
 * This demo uses httpbin.org: A simple HTTP Request & Response Service.
 */
#define SERVER_HOST           "httpbin.org"

/**
 * @brief The length of the HTTP server host name.
 */
#define SERVER_HOST_LENGTH    ( sizeof( SERVER_HOST ) - 1 )

/**
 * @brief HTTP server port number.
 *
 * In general, port 443 is for TLS HTTP connections.
 */
#define SERVER_PORT           443

/**
 * @brief Server's root CA certificate for TLS server authentication.
 *
 * This certificate should be PEM-encoded.
 */
#define SERVER_CERTIFICATE                                             \
    "-----BEGIN CERTIFICATE-----\n"                                    \
    "MIIDSjCCAjKgAwIBAgIQRK+wgNajJ7qJMDmGLvhAazANBgkqhkiG9w0BAQUFADA/" \
    "MSQwIgYDVQQKExtEaWdpdGFsIFNpZ25hdHVyZSBUcnVzdCBDby4xFzAVBgNVBAMT" \
    "DkRTVCBSb290IENBIFgzMB4XDTAwMDkzMDIxMTIxOVoXDTIxMDkzMDE0MDExNVow" \
    "PzEkMCIGA1UEChMbRGlnaXRhbCBTaWduYXR1cmUgVHJ1c3QgQ28uMRcwFQYDVQQD" \
    "Ew5EU1QgUm9vdCBDQSBYMzCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEB" \
    "AN+v6ZdQCINXtMxiZfaQguzH0yxrMMpb7NnDfcdAwRgUi+DoM3ZJKuM/IUmTrE4O" \
    "rz5Iy2Xu/NMhD2XSKtkyj4zl93ewEnu1lcCJo6m67XMuegwGMoOifooUMM0RoOEq" \
    "OLl5CjH9UL2AZd+3UWODyOKIYepLYYHsUmu5ouJLGiifSKOeDNoJjj4XLh7dIN9b" \
    "xiqKqy69cK3FCxolkHRyxXtqqzTWMIn/5WgTe1QLyNau7Fqckh49ZLOMxt+/yUFw" \
    "7BZy1SbsOFU5Q9D8/RhcQPGX69Wam40dutolucbY38EVAjqr2m7xPi71XAicPNaD" \
    "aeQQmxkqtilX4+U9m5/wAl0CAwEAAaNCMEAwDwYDVR0TAQH/BAUwAwEB/zAOBgNV" \
    "HQ8BAf8EBAMCAQYwHQYDVR0OBBYEFMSnsaR7LHH62+FLkHX/xBVghYkQMA0GCSqG" \
    "SIb3DQEBBQUAA4IBAQCjGiybFwBcqR7uKGY3Or+Dxz9LwwmglSBd49lZRNI+DT69" \
    "ikugdB/OEIKcdBodfpga3csTS7MgROSR6cz8faXbauX+5v3gTt23ADq1cEmv8uXr" \
    "AvHRAosZy5Q6XkjEGB5YGV8eAlrwDPGxrancWYaLbumR9YbK+rlmM6pZW87ipxZz" \
    "R8srzJmwN0jP41ZL9c8PDHIyh8bwRLtTcm1D9SZImlJnt1ir/md2cXjbDaJWFBM5" \
    "JDGFoqgCWjBH4d1QB7wCCZAA62RjYJsWvIjJEubSfZGL+T0yjWW06XyxV3bqxbYo" \
    "Ob8VZRzI9neWagqNdwvYkQsEjgfbKbYK7p2CNTUQ\n"                       \
    "-----END CERTIFICATE-----"

/**
 * @brief Length of the server's root CA certificate.
 */
#define SERVER_CERTIFICATE_LENGTH    ( sizeof( SERVER_CERTIFICATE ) - 1 )

/**
 * @brief Client's certificate for TLS client authentication.
 *
 * For the purposes of this demo, a self-signed certificate is used. However,
 * in practice, this certificate should be signed by a certifying authority
 * that is trusted by the server.
 *
 * This certificate should be PEM-encoded.
 */
#define CLIENT_CERTIFICATE                                             \
    "-----BEGIN CERTIFICATE-----\n"                                    \
    "MIID7jCCAtagAwIBAgIJAIosbgWzSgsKMA0GCSqGSIb3DQEBCwUAMIGLMQswCQYD" \
    "VQQGEwJVUzETMBEGA1UECAwKV2FzaGluZ3RvbjEQMA4GA1UEBwwHU2VhdHRsZTEP" \
    "MA0GA1UECgwGQW1hem9uMQwwCgYDVQQLDANBV1MxEzARBgNVBAMMCmFtYXpvbi5j" \
    "b20xITAfBgkqhkiG9w0BCQEWEnByaW1hcnlAYW1hem9uLmNvbTAeFw0yMDA2MDIw" \
    "MTE4MDdaFw00NzEwMTgwMTE4MDdaMIGLMQswCQYDVQQGEwJVUzETMBEGA1UECAwK" \
    "V2FzaGluZ3RvbjEQMA4GA1UEBwwHU2VhdHRsZTEPMA0GA1UECgwGQW1hem9uMQww" \
    "CgYDVQQLDANBV1MxEzARBgNVBAMMCmFtYXpvbi5jb20xITAfBgkqhkiG9w0BCQEW" \
    "EnByaW1hcnlAYW1hem9uLmNvbTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoC" \
    "ggEBAOZaC9kxlypwTRnLcPugCA52BnJDP2e6YmSj687uakBTqXCJk2gFeq7+nVRB" \
    "mDCzYs3eO+l0+xVMTwElJV5DAWvd14CHhxZ9tFqbzOuRUskHPzLvDjkPWoR6buKV" \
    "SdoE3KnFyNh0H5MO6Acq3G/IsT+ubBfIwA0kd4z11HS1rn9il/enmxeVipEM64qa" \
    "qBbd70T8I9nGku2zxkQKpY58VbbHTTybDEDNN519yFB+JtIE49PjU/O//gY381KA" \
    "h0cFrXWROnq1SxQmkvpz6iF8ovl9qdYUdZ6UO+dft5IEN+AR0sYdmMMnVude7jJ2" \
    "IkXh3xlZvKT5ciBFfhRGmqKVOPECAwEAAaNTMFEwHQYDVR0OBBYEFJeFbrDFIrQI" \
    "x928+SjsmrTvWs/eMB8GA1UdIwQYMBaAFJeFbrDFIrQIx928+SjsmrTvWs/eMA8G" \
    "A1UdEwEB/wQFMAMBAf8wDQYJKoZIhvcNAQELBQADggEBADb2qq9ONM44hWtdccV7" \
    "jVk9sHFffcXISgVAb9w8/ASHtHb80M6dedT/vYHS43IYCijtwwX8p/VyZo8TBdLf" \
    "fhLPi5EMXIxWYnG6/w+L97c0hkuKrzd0eIhgYrqwrmu3jvuA+HKfm14rOiGa/q4f" \
    "TU3//kOzcFCaDBZ+ecM9huKpRMr7gDMOzVsbwO/1BGXQDMY2lc1osozCOmvcDslj" \
    "0fS3IQO4MkIFHEdZkZBqPL/TuWi80OFYmvv/OSawoapUQGDotPEzzj6Xqrefl/cG" \
    "Jvsyun4fEeT9KUwYNWLDvNpBinYYzgq74EBK5mS/Idy9KoATv7SH3SngT6j89fo3" \
    "nRw=\n"                                                           \
    "-----END CERTIFICATE-----"

/**
 * @brief Length of the client's certificate.
 */
#define CLIENT_CERTIFICATE_LENGTH    ( sizeof( CLIENT_CERTIFICATE ) - 1 )

/**
 * @brief Client's key for TLS client authentication.
 *
 * This key should be PEM-encoded.
 */
#define CLIENT_KEY                                                     \
    "-----BEGIN PRIVATE KEY-----\n"                                    \
    "MIIEvAIBADANBgkqhkiG9w0BAQEFAASCBKYwggSiAgEAAoIBAQDmWgvZMZcqcE0Z" \
    "y3D7oAgOdgZyQz9numJko+vO7mpAU6lwiZNoBXqu/p1UQZgws2LN3jvpdPsVTE8B" \
    "JSVeQwFr3deAh4cWfbRam8zrkVLJBz8y7w45D1qEem7ilUnaBNypxcjYdB+TDugH" \
    "KtxvyLE/rmwXyMANJHeM9dR0ta5/Ypf3p5sXlYqRDOuKmqgW3e9E/CPZxpLts8ZE" \
    "CqWOfFW2x008mwxAzTedfchQfibSBOPT41Pzv/4GN/NSgIdHBa11kTp6tUsUJpL6" \
    "c+ohfKL5fanWFHWelDvnX7eSBDfgEdLGHZjDJ1bnXu4ydiJF4d8ZWbyk+XIgRX4U" \
    "RpqilTjxAgMBAAECggEALgpzcc7qou3dSzmRdImw8or+kNoGE0p6nhjxaePXUtIl" \
    "/LtSvijSM6XqdkvCCoHgTruLiAb8pG4jIFx3Upbb8t5dU3BDPOiVIsMfOzpJrKqJ" \
    "JDoJwrfh5La/8QPbxfrQzBIfKbxUD0WcdMpJUwJvAwZuznYuhLH0PzVnaIhjv0vp" \
    "dtR4ncCiemqp1lxdLi0mVyFQ9N/tYshza8E9hs1Ukv4mEIuiw3126DB4DVlIpuDj" \
    "+Ejp4SSY3ZTgG57dtXTri0U73jCCK/BOoSnn3mBYT+oysDOv/pZtceEz1QEn+7iC" \
    "iZy23F5BUZ7lHHNGa5TPNATSqyvum9W2HwuPH4Lr/QKBgQDzlzV7CHJIFbysaMsq" \
    "mhTO3DYp4fNA72XV929xEi+NFykFe/ZSL/r7iq01z3BH51O56y0JfIZCQhPzEYim" \
    "UOJlGCHWo3/9m7IKHTajFEKnoPnt/HwR+rgK7KT8GLQh5LXdtLdYtUXorQVtcsmQ" \
    "gA71O7f4aQ9f8dMrxGLuPNlSAwKBgQDyFi6OAaDXcOnfd14vop2I2BmF6ki7fqZP" \
    "btBgmCb1rzgqHGzslUhO/5OciJJlI2CHwN197C8VBIqcPXhy5+Xbhg0BZFMFbK5B" \
    "RGsgO5lXLOwzkMTYxz6/mgkCc6U8riwhHdf75422YobeWvCBTOdmOWhVmTkC7Csb" \
    "IESlFjXw+wKBgHsfxRKJNGqnQhTLa1X/R+E/gcktwmziFNFQHm5CyPJB8KQrAliM" \
    "lAotEFwQnCpcDP/+lWckICDBkZ/dDvsyCx0aU5BQWFNyLU3bclB/3yknvuzCIFxe" \
    "JESxVLtwKSywlBSaUcpu5gUz33hw+t0lPWpLYzQWtoTCkQCgZXkSHK7NAoGAATgP" \
    "X/OuJaeR5egp9z9wX6IG7t+xIhCPMdMzBWl+uLn7JGskOUS/Knaq/ZzKb+vvrn9Q" \
    "HjQ0QHzXXdYJZzq3s5VHN3yT1nEnp3h6uZzTNtcpEVFnTFgkfr590R9X86hE3J3T" \
    "2pbd5c81MqVulJgYijE7z0KIQPWDeg19iv9DokUCgYBRyI0O2oFsaa1trIXF3UbG" \
    "XxllW2WY0pgFpU8vADy2lwZmMusTY+lfuZPCIHkhoBy0mfpH8MMZIvh4ej2rYxf1" \
    "NbnJzabCy+sLb+z8S9aKHctfSruqsFLwYC0j+92gzrddDf+rimck9KylJ9dd1woI" \
    "nruOeU+ikSXECDw/PkPa/w==\n"                                       \
    "-----END PRIVATE KEY-----"

/**
 * @brief Length of the client's key.
 */
#define CLIENT_KEY_LENGTH    ( sizeof( CLIENT_KEY ) - 1 )

/**
 * @brief Paths for different HTTP methods for specified host.
 *
 * For httpbin.org, see http://httpbin.org/#/HTTP_Methods for details on
 * supported REST API.
 */
#ifndef GET_PATH
    #define GET_PATH    "/get"
#endif

#ifndef HEAD_PATH
    #define HEAD_PATH    "/get"
#endif

#ifndef PUT_PATH
    #define PUT_PATH    "/put"
#endif

#ifndef POST_PATH
    #define POST_PATH    "/post"
#endif

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define USER_BUFFER_LENGTH                ( 1024 )

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LEN           ( 40 )

/**
 * @brief Request body to send for PUT and POST requests in this demo.
 */
#define REQUEST_BODY                      "Hello, world!"

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH               ( sizeof( REQUEST_BODY ) - 1 )

#endif /* ifndef DEMO_CONFIG_H */
