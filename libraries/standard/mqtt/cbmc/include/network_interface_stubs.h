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

/**
 * @file network_interface_stubs.h
 * @brief Stub definitions for the application defined transport interface send
 * and receive callback.
 */
#ifndef NETWORK_INTERFACE_STUBS_H_
#define NETWORK_INTERfACE_STUBS_H_

/* mqtt.h must preceed including this header. */

/**
 * @brief Application defined network interface receive function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[out] pBuffer MQTT network receive buffer.
 * @param[in] bytesToRecv MQTT requested bytes.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                     void * pBuffer,
                                     size_t bytesToRecv );

/**
 * @brief Application defined network interface send function.
 *
 * @param[in] pNetworkContext Application defined network interface context.
 * @param[out] pBuffer MQTT network send buffer.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return Any value from INT32_MIN to INT32_MAX.
 */
int32_t NetworkInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                  const void * pBuffer,
                                  size_t bytesToSend );

#endif /* ifndef NETWORK_INTERFACE_STUBS_H_ */
