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

#include "mqtt.h"
#include "network_interface_stubs.h"

int32_t NetworkInterfaceReceiveStub( NetworkContext_t * pNetworkContext,
                                     void * pBuffer,
                                     size_t bytesToRecv )
{
    __CPROVER_assert( pBuffer != NULL,
                      "NetworkInterfaceReceiveStub pBuffer is not NULL." );

    __CPROVER_assert( __CPROVER_w_ok( pBuffer, bytesToRecv ),
                      "NetworkInterfaceReceiveStub pBuffer is writable up to bytesToRecv." );

    __CPROVER_havoc_object( pBuffer );

    /* This is unbounded as the MQTT code should be able to safely handle any
     * int32_t value returned from the application defined network receive
     * implementation. */
    int32_t bytesOrError;

    return bytesOrError;
}

int32_t NetworkInterfaceSendStub( NetworkContext_t * pNetworkContext,
                                  const void * pBuffer,
                                  size_t bytesToSend )
{
    __CPROVER_assert( pBuffer != NULL,
                      "NetworkInterfaceSendStub pBuffer is not NULL." );

    /* This is unbounded as the MQTT code should be able to safely handle any
     * int32_t value returned from the application defined network send
     * implementation. */
    int32_t bytesOrError;

    return bytesOrError;
}
