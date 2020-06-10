#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

/****************************************************************
* Bound the lengths of subscription and operation lists.
*
* Lists are empty by default.
* Set this variable to L+1 for lists of length <= L.
****************************************************************/

#ifndef SUBSCRIPTION_COUNT_MAX
    #define SUBSCRIPTION_COUNT_MAX    1
#endif

#ifndef OPERATION_COUNT_MAX
    #define OPERATION_COUNT_MAX    1
#endif

/****************************************************************
* Model a malloc that can fail and return NULL.
****************************************************************/

void * malloc_can_fail( size_t size )
{
    __CPROVER_assert( VALID_CBMC_SIZE( size ), "malloc_can_fail size too big" );
    return nondet_bool() ? NULL : malloc( size );
}

/****************************************************************
* Model an opaque type as nothing but a valid pointer.
****************************************************************/

void * allocate_opaque_type()
{
    return malloc( 1 ); /* consider using malloc(0) */
}

/****************************************************************
* MqttOperation
****************************************************************/

IotMqttOperation_t allocate_IotMqttOperation( IotMqttOperation_t pOp,
                                              IotMqttConnection_t pConn )
{
    /* assume a valid connection for the operation */
    assert( pConn != NULL );

    if( pOp == NULL )
    {
        pOp = malloc_can_fail( sizeof( *pOp ) );
    }

    if( pOp == NULL )
    {
        return NULL;
    }

    pOp->pMqttConnection = pConn;

    if( pOp->incomingPublish )
    {
        /* allocate publish member of the union */

        allocate_IotMqttPublishInfo( &( pOp->u.publish.publishInfo ) );

        size_t length;
        __CPROVER_assume( VALID_CBMC_SIZE( length ) );
        pOp->u.publish.pReceivedData = malloc_can_fail( length );
    }
    else
    {
        /* allocate operation member of the union */

        /* assumption here is checked below in valid_* */
        __CPROVER_assume( VALID_CBMC_SIZE( pOp->u.operation.packetSize ) );
        pOp->u.operation.pMqttPacket =
            malloc_can_fail( pOp->u.operation.packetSize );
    }

    return pOp;
}

/* TODO: valid_ should have same signature as allocate_, */
/* should check that operation points to the connection */

bool valid_IotMqttOperation( const IotMqttOperation_t pOp )
{
    if( pOp == NULL )
    {
        return false;
    }

    /* publish member of the union should be valid (pOp->incomingPublish ) */

    bool valid_publishinfo =
        valid_IotMqttPublishInfo( &( pOp->u.publish.publishInfo ) );

    bool valid_publish_member =
        IMPLIES( pOp->incomingPublish, valid_publishinfo );

    /* operation member of the union should be valid (!pOp->incomingPublish) */

    bool valid_packet =
        VALID_STRING( pOp->u.operation.pMqttPacket, pOp->u.operation.packetSize ) &&
        #ifdef PACKET_SIZE_MAX
            /* Some proofs iterate over a packet and must bound the packet size */
            pOp->u.operation.packetSize < PACKET_SIZE_MAX &&
        #endif
        VALID_CBMC_SIZE( pOp->u.operation.packetSize );
    bool valid_pingreq_packet =
        IMPLIES( pOp->u.operation.type == IOT_MQTT_PINGREQ,
                 IFF( pOp->u.operation.periodic.ping.keepAliveMs == 0,
                      pOp->u.operation.packetSize == 0 ) );
    bool valid_other_packet =
        IMPLIES( pOp->u.operation.type != IOT_MQTT_PINGREQ,
                 pOp->u.operation.packetSize > 0 );
    bool waitable =
        ( pOp->u.operation.flags & IOT_MQTT_FLAG_WAITABLE )
        == IOT_MQTT_FLAG_WAITABLE;
    /* Async operations are waitable.  Loosely speaking, an async operation */
    /* is split into independent send and ack events, and an sync operation */
    /* is not. */
    bool valid_jobReference;

    /* Implication is most natural here, but the use of it with __CPROVER_assume */
    /* leads to inconsistent values in jobReferences. */
    if( waitable )
    {
        valid_jobReference = ( pOp->u.operation.jobReference == 2 );
    }
    else
    {
        valid_jobReference = ( pOp->u.operation.jobReference == 1 );
    }

    bool valid_operation_member =
        IMPLIES( !pOp->incomingPublish,
                 valid_packet &&
                 valid_pingreq_packet &&
                 valid_other_packet &&
                 valid_jobReference );

    return
        /* assume valid connection */
        valid_publish_member &&
        valid_operation_member;
}

/****************************************************************
* IotMqttOperation list
****************************************************************/

IotListDouble_t * allocate_IotMqttOperationList( IotListDouble_t * pOp,
                                                 size_t length,
                                                 IotMqttConnection_t pConn )
{
    /* Allocate lists of length L <= 3 (MAX = L+1) */
    __CPROVER_assert( length < OPERATION_COUNT_MAX,
                      "Operation list length max is greater than MAX" );
    __CPROVER_assert( length <= 3,
                      "Operation list length max is greater than 3" );

    if( pOp == NULL )
    {
        pOp = malloc_can_fail( sizeof( *pOp ) );
    }

    if( pOp == NULL )
    {
        return NULL;
    }

    IotListDouble_Create( pOp );

    size_t numElts;
    __CPROVER_assume( numElts <= length );

    IotMqttOperation_t pElt;

    switch( numElts )
    {
        #if 3 < OPERATION_COUNT_MAX
            case 3:
                pElt = allocate_IotMqttOperation( NULL, pConn );
                __CPROVER_assume( pElt );
                IotListDouble_InsertHead( pOp, &( pElt->link ) );
        #endif
        #if 2 < OPERATION_COUNT_MAX
            case 2:
                pElt = allocate_IotMqttOperation( NULL, pConn );
                __CPROVER_assume( pElt );
                IotListDouble_InsertHead( pOp, &( pElt->link ) );
        #endif
        #if 1 < OPERATION_COUNT_MAX
            case 1:
                pElt = allocate_IotMqttOperation( NULL, pConn );
                __CPROVER_assume( pElt );
                IotListDouble_InsertHead( pOp, &( pElt->link ) );
        #endif
        default:
            ;
    }

    return pOp;
}

bool valid_IotMqttOperationList( const IotListDouble_t * pOp,
                                 const size_t length )
{
    if( pOp == NULL )
    {
        return false;
    }

    /* TODO: Consider replacing loop with straight line code */

    IotListDouble_t * pLink;
    IotContainers_ForEach( pOp, pLink )
    {
        IotMqttOperation_t * pElt = IotLink_Container( struct _mqttOperation, pLink, link );

        if( !valid_IotMqttOperation( pElt ) )
        {
            return false;
        }
    }

    return
        /* MAX is one greater than the maximum length */
        length < OPERATION_COUNT_MAX;
}

/****************************************************************
* IotMqttConnection
****************************************************************/

IotMqttConnection_t allocate_IotMqttConnection( IotMqttConnection_t pConn )
{
    if( pConn == NULL )
    {
        pConn = malloc_can_fail( sizeof( *pConn ) );
    }

    if( pConn == NULL )
    {
        return NULL;
    }

    pConn->pNetworkConnection = allocate_IotNetworkConnection();
    pConn->pNetworkInterface = allocate_IotNetworkInterface();
    allocate_IotMqttOperation( &( pConn->pingreq ), pConn );
    allocate_IotMqttCallbackInfo( &( pConn->disconnectCallback ) );
    return pConn;
}

IotMqttConnection_t ensure_IotMqttConnection_has_lists( IotMqttConnection_t pConn )
{
    allocate_IotMqttOperationList( &pConn->pendingProcessing,
                                   OPERATION_COUNT_MAX - 1,
                                   pConn );
    allocate_IotMqttOperationList( &pConn->pendingResponse,
                                   OPERATION_COUNT_MAX - 1,
                                   pConn );
    allocate_IotMqttSubscriptionList( &pConn->subscriptionList,
                                      SUBSCRIPTION_COUNT_MAX - 1 );
    return pConn;
}

bool valid_IotMqttConnection( const IotMqttConnection_t pConn )
{
    if( pConn == NULL )
    {
        return false;
    }

    /* This is the number of callbacks and operations using the connection. */
    /* It is a uint32 and must be bounded by a number smaller than the */
    /* maximum value to avoid integer overflows.  We expect to run out of */
    /* memory before having 2^16 references on a device. */
    bool valid_references = pConn->references >= 0 &&
                            pConn->references <= ( 1 << 16 );

    bool valid_pingreq =
        ( valid_IotMqttOperation( &( pConn->pingreq ) ) ) &&
        ( pConn->pingreq.u.operation.type == IOT_MQTT_PINGREQ ) &&
        ( pConn->pingreq.pMqttConnection == pConn ) &&
        ( !pConn->pingreq.incomingPublish );

    return
        valid_IotMqttOperationList( &pConn->pendingProcessing,
                                    OPERATION_COUNT_MAX - 1 ) &&
        valid_IotMqttOperationList( &pConn->pendingResponse,
                                    OPERATION_COUNT_MAX - 1 ) &&
        valid_IotMqttSubscriptionList( &pConn->subscriptionList,
                                       SUBSCRIPTION_COUNT_MAX - 1 ) &&
        valid_IotNetworkInterface( pConn->pNetworkInterface ) &&
        valid_references &&
        valid_pingreq;
}

/****************************************************************
* IotMqttNetworkInfo
****************************************************************/

IotMqttNetworkInfo_t * allocate_IotMqttNetworkInfo( IotMqttNetworkInfo_t * pInfo )
{
    if( pInfo == NULL )
    {
        pInfo = malloc_can_fail( sizeof( *pInfo ) );
    }

    if( pInfo == NULL )
    {
        return NULL;
    }

    if( pInfo->createNetworkConnection )
    {
        /* allocate setup member of union */
        pInfo->u.setup.pNetworkServerInfo = allocate_opaque_type();
        pInfo->u.setup.pNetworkCredentialInfo = allocate_opaque_type();
    }
    else
    {
        /* allocate network member of union */
        pInfo->u.pNetworkConnection = allocate_IotNetworkConnection();
    }

    pInfo->pNetworkInterface = allocate_IotNetworkInterface();
    return pInfo;
}

bool valid_IotMqttNetworkInfo( const IotMqttNetworkInfo_t * pInfo )
{
    return pInfo != NULL;
}

/****************************************************************
* IotMqttConnectInfo
****************************************************************/

void bound_IotMqttConnectInfo( IotMqttConnectInfo_t * pInfo )
{
    #ifdef SUBSCRIPTION_COUNT_MAX
        __CPROVER_assume( pInfo->previousSubscriptionCount < SUBSCRIPTION_COUNT_MAX );
    #endif

    #ifdef CLIENT_IDENTIFIER_LENGTH_MAX
        __CPROVER_assume( pInfo->clientIdentifierLength < CLIENT_IDENTIFIER_LENGTH_MAX &&
                          VALID_CBMC_SIZE( pInfo->clientIdentifierLength ) );
    #else
        __CPROVER_assume( pInfo->clientIdentifierLength <= UINT16_MAX );
    #endif

    #ifdef USER_NAME_LENGTH_MAX
        __CPROVER_assume( pInfo->userNameLength < USER_NAME_LENGTH_MAX &&
                          VALID_CBMC_SIZE( pInfo->userNameLength ) );
    #else
        __CPROVER_assume( pInfo->userNameLength <= UINT16_MAX );
    #endif

    #ifdef PASSWORD_LENGTH_MAX
        __CPROVER_assume( pInfo->passwordLength < PASSWORD_LENGTH_MAX &&
                          VALID_CBMC_SIZE( pInfo->passwordLength ) );
    #else
        __CPROVER_assume( pInfo->passwordLength <= UINT16_MAX );
    #endif
}

IotMqttConnectInfo_t * allocate_IotMqttConnectInfo( IotMqttConnectInfo_t * pInfo )
{
    if( pInfo == NULL )
    {
        pInfo = malloc_can_fail( sizeof( *pInfo ) );
    }

    if( pInfo == NULL )
    {
        return NULL;
    }

    bound_IotMqttConnectInfo( pInfo );

    pInfo->pPreviousSubscriptions =
        allocate_IotMqttSubscriptionArray( NULL,
                                           pInfo->previousSubscriptionCount );

    pInfo->pWillInfo = allocate_IotMqttPublishInfo( NULL );
    pInfo->pClientIdentifier = malloc_can_fail( pInfo->clientIdentifierLength );
    pInfo->pUserName = malloc_can_fail( pInfo->userNameLength );
    pInfo->pPassword = malloc_can_fail( pInfo->passwordLength );

    return pInfo;
}

bool valid_IotMqttConnectInfo( const IotMqttConnectInfo_t * pInfo )
{
    return
        pInfo != NULL &&

        valid_IotMqttPublishInfo( pInfo->pWillInfo ) &&

        IFF( pInfo->pPreviousSubscriptions == NULL,
             pInfo->previousSubscriptionCount == 0 ) &&
        valid_IotMqttSubscriptionArray( pInfo->pPreviousSubscriptions,
                                        pInfo->previousSubscriptionCount );
}

/****************************************************************
* IotMqttSubscription
****************************************************************/

IotMqttSubscription_t * allocate_IotMqttSubscription( IotMqttSubscription_t * pSub )
{
    if( pSub == NULL )
    {
        pSub = malloc_can_fail( sizeof( *pSub ) );
    }

    if( pSub == NULL )
    {
        return NULL;
    }

    pSub->pTopicFilter = malloc_can_fail( pSub->topicFilterLength );
    return pSub;
}

bool valid_IotMqttSubscription( const IotMqttSubscription_t * pSub )
{
    return
        pSub != NULL &&

        VALID_STRING( pSub->pTopicFilter, pSub->topicFilterLength ) &&
        VALID_CBMC_SIZE( pSub->topicFilterLength )

        #ifdef TOPIC_LENGTH_MAX
            /* MAX is one greater than the maximum length */
            && pSub->topicFilterLength < TOPIC_LENGTH_MAX
        #endif
    ;
}

/****************************************************************
* IotMqttSubscription array list
****************************************************************/

IotMqttSubscription_t * allocate_IotMqttSubscriptionArray( IotMqttSubscription_t * pSub,
                                                           size_t length )
{
    /* Allocate lists of length L <= 3 (MAX = L+1) */
    __CPROVER_assert( length < SUBSCRIPTION_COUNT_MAX,
                      "Subscription array length max is greater than MAX" );
    __CPROVER_assert( length <= 3,
                      "Subscription array length max is greater than 3" );

    if( pSub == NULL )
    {
        pSub = malloc_can_fail( length * sizeof( *pSub ) );
    }

    if( pSub == NULL )
    {
        return NULL;
    }

    switch( length )
    {
        #if 3 < SUBSCRIPTION_COUNT_MAX
            case 3:
                allocate_IotMqttSubscription( pSub + 2 );
        #endif
        #if 2 < SUBSCRIPTION_COUNT_MAX
            case 2:
                allocate_IotMqttSubscription( pSub + 1 );
        #endif
        #if 1 < SUBSCRIPTION_COUNT_MAX
            case 1:
                allocate_IotMqttSubscription( pSub + 0 );
        #endif
        default:
            ;
    }

    return pSub;
}
bool valid_IotMqttSubscriptionArray( const IotMqttSubscription_t * pSub,
                                     const size_t length )
{
    if( !IFF( ( pSub == NULL ), ( length == 0 ) ) )
    {
        return false;
    }

    if( pSub == NULL )
    {
        return false;
    }

    /* TODO: Consider replacing loop with straight line code */

    for( size_t i = 0; i < length; i++ )
    {
        if( !valid_IotMqttSubscription( pSub + i ) )
        {
            return false;
        }
    }

    return
        /* MAX is one greater than the maximum length */
        length < SUBSCRIPTION_COUNT_MAX;
}

/****************************************************************
* IotMqttSubscription array list
****************************************************************/

/* Subscription linked list elements */

_mqttSubscription_t * allocate_IotMqttSubscriptionListElt( _mqttSubscription_t * pElt )
{
    uint16_t length;

    if( pElt == NULL )
    {
        pElt = malloc_can_fail( sizeof( *pElt ) + length );
    }

    if( pElt == NULL )
    {
        return NULL;
    }

    /* References must never be negative */
    __CPROVER_assume( pElt->references >= 0 );
    pElt->link.pPrevious = NULL;
    pElt->link.pNext = NULL;
    pElt->topicFilterLength = length;
    /* pElt->topicFilter is a flexible struct member following pElt */
    return pElt;
}

bool valid_IotMqttSubscriptionListElt( const _mqttSubscription_t * pElt )
{
    if( pElt == NULL )
    {
        return false;
    }

    return
        #ifdef TOPIC_LENGTH_MAX
            /* MAX is one greater than the maximum length */
            pElt->topicFilterLength < TOPIC_LENGTH_MAX &&
        #endif
        pElt->topicFilterLength < CBMC_MAX_OBJECT_SIZE - sizeof( *pElt );
}

/* Subscription linked lists */

IotListDouble_t * allocate_IotMqttSubscriptionList( IotListDouble_t * pSub,
                                                    size_t length )
{
    /* Allocate lists of length L <= 3 (MAX = L+1) */
    __CPROVER_assert( length < SUBSCRIPTION_COUNT_MAX,
                      "Subscription list length max is greater than MAX" );
    __CPROVER_assert( length <= 3,
                      "Subscription list length max is greater than 3" );

    if( pSub == NULL )
    {
        pSub = malloc_can_fail( sizeof( *pSub ) );
    }

    if( pSub == NULL )
    {
        return NULL;
    }

    IotListDouble_Create( pSub );

    size_t numElts;
    __CPROVER_assume( numElts <= length );

    _mqttSubscription_t * pElt;

    switch( numElts )
    {
        #if 3 < SUBSCRIPTION_COUNT_MAX
            case 3:
                pElt = allocate_IotMqttSubscriptionListElt( NULL );
                __CPROVER_assume( pElt );
                IotListDouble_InsertHead( pSub, &( pElt->link ) );
        #endif
        #if 2 < SUBSCRIPTION_COUNT_MAX
            case 2:
                pElt = allocate_IotMqttSubscriptionListElt( NULL );
                __CPROVER_assume( pElt );
                IotListDouble_InsertHead( pSub, &( pElt->link ) );
        #endif
        #if 1 < SUBSCRIPTION_COUNT_MAX
            case 1:
                pElt = allocate_IotMqttSubscriptionListElt( NULL );
                __CPROVER_assume( pElt );
                IotListDouble_InsertHead( pSub, &( pElt->link ) );
        #endif
        default:
            ;
    }

    return pSub;
}
bool valid_IotMqttSubscriptionList( const IotListDouble_t * pSub,
                                    const size_t length )
{
    if( pSub == NULL )
    {
        return false;
    }

    /* TODO: Consider replacing loop with straight line code */

    IotListDouble_t * pLink;
    IotContainers_ForEach( pSub, pLink )
    {
        _mqttSubscription_t
        * pElt = IotLink_Container( _mqttSubscription_t, pLink, link );

        if( !valid_IotMqttSubscriptionListElt( pElt ) )
        {
            return false;
        }
    }

    return
        /* MAX is one greater than the maximum length */
        length < SUBSCRIPTION_COUNT_MAX;
}

void * invalid_pointer()
{
    void * ptr;

    return ptr;
}

void free_IotMqttSubscriptionList( IotListDouble_t * pSub )
{
    IotListDouble_t * pThis;
    IotListDouble_t * pNext;

    if( pSub == NULL )
    {
        return;
    }

    pThis = pSub->pNext;
    pSub->pNext = invalid_pointer();
    pSub->pPrevious = invalid_pointer();

    #if 3 < SUBSCRIPTION_COUNT_MAX
        if( pThis == pSub )
        {
            return;
        }

        pNext = pThis->pNext;
        free( IotLink_Container( _mqttSubscription_t, pThis, link ) );
        pThis = pNext;
    #endif

    #if 2 < SUBSCRIPTION_COUNT_MAX
        if( pThis == pSub )
        {
            return;
        }

        pNext = pThis->pNext;
        free( IotLink_Container( _mqttSubscription_t, pThis, link ) );
        pThis = pNext;
    #endif

    #if 1 < SUBSCRIPTION_COUNT_MAX
        if( pThis == pSub )
        {
            return;
        }

        pNext = pThis->pNext;
        free( IotLink_Container( _mqttSubscription_t, pThis, link ) );
        pThis = pNext;
    #endif

    /* The being freed could be longer than SUBSCRIPTION_COUNT_MAX:
     * Allocate a list of maximal length, then add one subscription, then free it. */
}


/****************************************************************
* IotMqttPublishInfo
****************************************************************/

void bound_IotMqttPublishInfo( IotMqttPublishInfo_t * pInfo )
{
    #ifdef TOPIC_NAME_LENGTH_MAX
        __CPROVER_assume( pInfo->topicNameLength < TOPIC_NAME_LENGTH_MAX &&
                          VALID_CBMC_SIZE( pInfo->topicNameLength ) );
    #else
        __CPROVER_assume( pInfo->topicNameLength <= UINT16_MAX );
    #endif

    #ifdef PAYLOAD_LENGTH_MAX
        __CPROVER_assume( pInfo->payloadLength < PAYLOAD_LENGTH_MAX &&
                          VALID_CBMC_SIZE( pInfo->payloadLength ) );
    #else
        __CPROVER_assume( pInfo->payloadLength <= UINT16_MAX );
    #endif
}

IotMqttPublishInfo_t * allocate_IotMqttPublishInfo( IotMqttPublishInfo_t * pInfo )
{
    if( pInfo == NULL )
    {
        pInfo = malloc_can_fail( sizeof( *pInfo ) );
    }

    if( pInfo == NULL )
    {
        return NULL;
    }

    bound_IotMqttPublishInfo( pInfo );

    pInfo->pTopicName = malloc_can_fail( pInfo->topicNameLength );
    pInfo->pPayload = malloc_can_fail( pInfo->payloadLength );
    return pInfo;
}

bool valid_IotMqttPublishInfo( const IotMqttPublishInfo_t * pInfo )
{
    return
        pInfo != NULL &&
        VALID_QOS( pInfo->qos ) &&
        pInfo->retryMs <= IOT_MQTT_RETRY_MS_CEILING;
}

/****************************************************************
* IotNetworkConnection
****************************************************************/

void * allocate_IotNetworkConnection()
{
    return allocate_opaque_type();
}

/****************************************************************
* IotNetworkInterface
****************************************************************/

IotNetworkInterface_t * allocate_IotNetworkInterface()
{
    return malloc_can_fail( sizeof( IotNetworkInterface_t ) );
}

bool valid_IotNetworkInterface( const IotNetworkInterface_t * netif )
{
    return( netif != NULL );
}

bool stubbed_IotNetworkInterface( const IotNetworkInterface_t * netif )
{
    return
        IS_STUBBED_NETWORKIF_CREATE( netif ) &&
        IS_STUBBED_NETWORKIF_CLOSE( netif ) &&
        IS_STUBBED_NETWORKIF_SEND( netif ) &&
        IS_STUBBED_NETWORKIF_RECEIVE( netif ) &&
        IS_STUBBED_NETWORKIF_SETRECEIVECALLBACK( netif ) &&
        IS_STUBBED_NETWORKIF_SETCLOSECALLBACK( netif ) &&
        IS_STUBBED_NETWORKIF_DESTROY( netif );
}

/****************************************************************
* IotNetworkInterface stubs
****************************************************************/

IotNetworkError_t IotNetworkInterfaceCreate( void * pConnectionInfo,
                                             void * pCredentialInfo,
                                             void * pConnection )
{
    /* pCredentialInfo can be null */
    /* create accepts NULL credentials when there is no TLS configuration. */
    __CPROVER_assert( pConnectionInfo != NULL,
                      "IotNetworkInterfaceCreate pConnectionInfo is not NULL" );
    __CPROVER_assert( pConnection != NULL,
                      "IotNetworkInterfaceCreate pConnection is not NULL" );

    /* create the connection */
    *( void ** ) pConnection = allocate_IotNetworkConnection();

    IotNetworkError_t error;
    return error;
}

#ifndef MAX_TRIES
    #define MAX_TRIES    2
#endif

size_t IotNetworkInterfaceSend( void * pConnection,
                                const uint8_t * pMessage,
                                size_t messageLength )
{
    __CPROVER_assert( pConnection != NULL,
                      "IotNetworkInterfaceSend pConnection is not NULL" );
    __CPROVER_assert( pMessage != NULL,
                      "IotNetworkInterfaceSend pMessage is not NULL" );

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
    static size_t tries;

    /* The number of bytes considered sent after this invocation */
    size_t size;

    if( ( tries >= MAX_TRIES ) || ( size > messageLength ) )
    {
        tries = 0;
        return messageLength;
    }

    tries++;
    return size;
}

IotNetworkError_t IotNetworkInterfaceClose( void * pConnection )
{
    __CPROVER_assert( pConnection != NULL,
                      "IotNetworkInterfaceClose pConnection is not NULL" );

    IotNetworkError_t error;
    return error;
}

size_t IotNetworkInterfaceReceive( void * pConnection,
                                   uint8_t * pBuffer,
                                   size_t bytesRequested )
{
    __CPROVER_assert( pConnection,
                      "IotNetworkInterfaceReceive pConnection is not NULL" );
    __CPROVER_assert( pBuffer,
                      "IotNetworkInterfaceReceive pBuffer is not NULL" );

    __CPROVER_havoc_object( pBuffer );

    /* Choose the number of bytes in pBuffer considered received. */
    size_t size;
    __CPROVER_assume( size <= bytesRequested );

    return size;
}

IotNetworkError_t IotNetworkInterfaceReceiveCallback( void * pConnection,
                                                      IotNetworkReceiveCallback_t
                                                      receiveCallback,
                                                      void * pContext )
{
    __CPROVER_assert( pConnection != NULL,
                      "IotNetworkInterfaceCallback pConnection is not NULL" );
    __CPROVER_assert( receiveCallback != NULL,
                      "IotNetworkInterfaceCallback receiveCallback is not NULL" );
    __CPROVER_assert( pContext != NULL,
                      "IotNetworkInterfaceCallback pContext is not NULL" );

    IotNetworkError_t error;
    return error;
}

IotNetworkError_t IotNetworkInterfaceCloseCallback( void * pConnection,
                                                    IotNetworkCloseCallback_t
                                                    closeCallback,
                                                    void * pContext )
{
    __CPROVER_assert( pConnection != NULL,
                      "IotNetworkInterfaceCallback pConnection is not NULL" );
    __CPROVER_assert( closeCallback != NULL,
                      "IotNetworkInterfaceCallback closeCallback is not NULL" );
    __CPROVER_assert( pContext != NULL,
                      "IotNetworkInterfaceCallback pContext is not NULL" );

    IotNetworkError_t error;
    return error;
}

IotNetworkError_t IotNetworkInterfaceDestroy( void * pConnection )
{
    __CPROVER_assert( pConnection != NULL,
                      "IotNetworkInterfaceDestroy pConnection is not NULL" );

    IotNetworkError_t error;
    return error;
}

/****************************************************************/

IotMqttCallbackInfo_t * allocate_IotMqttCallbackInfo( IotMqttCallbackInfo_t * pCb )
{
    if( pCb == NULL )
    {
        pCb = malloc_can_fail( sizeof( *pCb ) );
    }

    if( pCb == NULL )
    {
        return NULL;
    }

    pCb->pCallbackContext = allocate_opaque_type();
    pCb->function = nondet_bool() ? NULL : IotUserCallback;

    return pCb;
}

void IotUserCallback( void * pCallbackContext,
                      IotMqttCallbackParam_t * pCallbackParam )
{
    __CPROVER_assert( pCallbackContext != NULL,
                      "IotUserCallback pCallbackContext is not NULL" );
    __CPROVER_assert( pCallbackParam != NULL,
                      "IotUserCallback pCallbackParam is not NULL" );
}
