#include "transport_interface_stubs.h"

int32_t TransportInterfaceSendStub( NetworkContext_t * pContext,
                                    void * pBuffer,
                                    size_t bytesToSend )
{
    __CPROVER_assert( pBuffer != NULL,
                      "TransportInterfaceSendStub pBuffer is NULL" );

    /****************************************************************
    * The send method sends some portion of the message and returns the
    * total number of bytes in the prefix sent so far.  The send method
    * is used in a loop of the form
    *
    *   while ( send( conn, msg, len )  < len ) { ... }
    *
    * We need to bound the number of loop iterations, so we need to
    * bound the number of times it takes for send to finish sending the
    * message.  We use a static variable 'tries' to count the number of
    * times send has tried to send the message, and we force send to
    * finish the message after MAX_TRIES tries.
    ****************************************************************/

    /* The number of tries to send the message before this invocation */
    static int32_t tries;
    tries++;

    /* The number of bytes considered sent after this invocation */
    int32_t ret;

    if( tries >= MAX_TRIES )
    {
        if( bytesToSend > INT32_MAX )
        {
            ret = INT32_MAX;
        }
        else
        {
            tries = 0;
            ret = bytesToSend;
        }
    }

    return ret;
}

int32_t TransportInterfaceReceiveStub( NetworkContext_t * pContext,
                                       void * pBuffer,
                                       size_t bytesToRecv )
{
    __CPROVER_assert( pBuffer != NULL,
                      "TransportInterfaceReceiveStub pBuffer is NULL" );

    /* The number of bytes considered received after this invocation */
    int32_t ret;

    return ret;
}
