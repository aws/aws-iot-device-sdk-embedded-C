/*
 * AWS IoT Device SDK for Embedded C 202412.00
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

#ifndef AWS_IOT_ALPN_DEFS_H_
#define AWS_IOT_ALPN_DEFS_H_

/*
 * AWS IoT Core allows the use of HTTP or MQTT over TCP port 443. Connections
 * to IoT Core endpoints on port 443 default to the HTTP protocol.
 *
 * Clients must use the TLS Application-Layer Protocol Negotiation extension
 * to notify the service of it's desired protocol or authentication mode.
 *
 * For more information, please reference the following URL:
 * https://docs.aws.amazon.com/iot/latest/developerguide/protocols.html
 */

#define AWS_IOT_ALPN_MQTT_CUSTOM_AUTH                "mqtt"
#define AWS_IOT_ALPN_MQTT_CA_AUTH                    "x-amzn-mqtt-ca"
#define AWS_IOT_ALPN_HTTP_CA_AUTH                    "x-amzn-http-ca"

/*
 * @note OpenSSL requires that ALPN identifiers be provided in protocol form.
 *       This means that each alpn string be prepended with its length.
 *       When multiple concurrent alpn identifiers are necessary,
 *       each identifier should be prepended with it's respective length and
 *       then concatenated together.
 */
#define AWS_IOT_ALPN_MQTT_CUSTOM_AUTH_OPENSSL        "\x04mqtt"
#define AWS_IOT_ALPN_MQTT_CUSTOM_AUTH_OPENSSL_LEN    ( sizeof( AWS_IOT_ALPN_MQTT_CUSTOM_AUTH_OPENSSL ) - 1U )

#define AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL            "\x0ex-amzn-mqtt-ca"
#define AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL_LEN        ( sizeof( AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL ) - 1U )

#define AWS_IOT_ALPN_HTTP_CA_AUTH_OPENSSL            "\x0ex-amzn-http-ca"
#define AWS_IOT_ALPN_HTTP_CA_AUTH_OPENSSL_LEN        ( sizeof( AWS_IOT_ALPN_HTTP_CA_AUTH_OPENSSL ) - 1U )

/*
 * @note MbedTLS requires alpn identifiers to be provided in a null terminated
 *       array of null terminated c strings.
 */
#define AWS_IOT_ALPN_MQTT_CUSTOM_AUTH_MBEDTLS        { AWS_IOT_ALPN_MQTT_CUSTOM_AUTH, NULL }
#define AWS_IOT_ALPN_MQTT_CA_AUTH_MBEDTLS            { AWS_IOT_ALPN_MQTT_CA_AUTH, NULL }
#define AWS_IOT_ALPN_HTTP_CA_AUTH_MBEDTLS            { AWS_IOT_ALPN_HTTP_CA_AUTH, NULL }

#endif /* AWS_IOT_ALPN_DEFS_H_ */
