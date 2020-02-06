#include <stdlib.h>

/****************************************************************
 * Logical connectives useful in assuptions
 ****************************************************************/

#define IMPLIES(a, b) (!(a) || (b))
#define IFF(a, b) (IMPLIES(a, b) && IMPLIES(b, a))
//#define IFF(a, b) ((a) == (b))

/****************************************************************
 * String pointers satisfy an invariant that the pointer is null
 * iff the length is zero.  The string and length are typically
 * members of a struct, and this invariant is part of a validity
 * condition for the struct.
 ****************************************************************/

#define VALID_STRING(string, length) IFF((string) == NULL, (length) == 0)

/****************************************************************
 * There is a bound on the size of an object that can be modeled in
 * CBMC.  A point in CBMC consists of an object id and an offset
 * into the object.  The top few bits of a pointer are used to encode
 * the object id, leaving only the bottom remaining bits to encode
 * the object offset.  The number of bits used for the object id,
 * that thus the bound on the size of the object, is defined in the
 * Makefile.
 ****************************************************************/

#define VALID_CBMC_SIZE(size) ((size) < CBMC_MAX_OBJECT_SIZE)

/****************************************************************
 * Model a malloc that can fail and return NULL.  CBMC currently
 * models malloc as an allocator that never fails.  CBMC will soon
 * have an option to let malloc fail.
 ****************************************************************/

void *malloc_can_fail(size_t size);

/****************************************************************
 * Type allocators and validators
 *
 * For every type used by MQTT, like a connection or an operation, we
 * provide an allocator and a validator.  The purpose of the allocator
 * is simply to allocate on the heap the space for an unconstrained
 * value of the right shape.  The purpose of the validator is to state
 * restrictions on the possible values of the object.
 *
 * A type is typically a tree of structs and buffers and arrays.  The
 * allocator lays out space on the heap for this tree.  The allocator
 * may, however, prune the tree in arbitrary ways by inserting NULL
 * into a pointer in a struct intended to point to the children of the
 * struct.  The allocator may even prune away the entire tree and
 * return nothing but a NULL pointer.  If a proof requires that some
 * portion of the tree is not pruned away (that some pointer is not
 * NULL), this assumption must be made explicitly, either in the
 * validator or in the proof harness itself.
 *
 * Each allocator takes a pointer to the struct at the root of the
 * tree.  If that pointer is NULL, the allocator allocates the root
 * struct and the result of the tree.  If it points to an existing
 * root struct, the allocators uses that root and fills in the rest of
 * the tree.  The pointer is usually NULL.  In constrast, because a
 * connection struct includes an ping request operation struct as a
 * substruct, we allocate that ping request operation by passing a
 * pointer to the connection's operation substruct.
 ****************************************************************/

/****************************************************************
 * IotMqttConnection
 ****************************************************************/

IotMqttConnection_t allocate_IotMqttConnection( IotMqttConnection_t pConn );
bool valid_IotMqttConnection( IotMqttConnection_t pConn );
IotMqttConnection_t
  ensure_IotMqttConnection_has_lists( IotMqttConnection_t pConn );

/****************************************************************
 * MqttOperation
 *
 * A pending operation includes a pointer to its connection.  A
 * connection includes a list of all of its pending operations.  All
 * operations pending on a connection include a pointer to this
 * connection.  For this reason, the allocator for an operation takes
 * a reference to a connection.
 ****************************************************************/

IotMqttOperation_t allocate_IotMqttOperation( IotMqttOperation_t pOp,
					       IotMqttConnection_t pConn );
bool valid_IotMqttOperation( IotMqttOperation_t pOp );

/****************************************************************
 * IotMqttNetworkInfo
 ****************************************************************/

IotMqttNetworkInfo_t *allocate_IotMqttNetworkInfo(IotMqttNetworkInfo_t *pInfo);
bool valid_IotMqttNetworkInfo(IotMqttNetworkInfo_t *pInfo);

/****************************************************************
 * IotMqttConnectInfo
 ****************************************************************/

IotMqttConnectInfo_t *allocate_IotMqttConnectInfo(IotMqttConnectInfo_t *pInfo);
bool valid_IotMqttConnectInfo(IotMqttConnectInfo_t *pInfo);

/****************************************************************
 * IotMqttSubscription
 *
 * A client subscribes to a topic represented by a string.  For some
 * proofs, we need to bound the length of this string (for example,
 * when we have to unwind a loop in a function that iterates over the
 * string).  When we need to bound the length for a proof, we define
 * TOPIC_LENGTH_MAX in the proof's Makefile.
 ****************************************************************/

IotMqttSubscription_t *allocate_IotMqttSubscription(IotMqttSubscription_t *pSub);
bool valid_IotMqttSubscription(IotMqttSubscription_t *pSub);

/****************************************************************
 * IotMqttSubscription list
 *
 * There are two kinds of subscription lists in MQTT: array lists and
 * linked lists.
 *
 * For some proofs, we need to bound the length of the list.  For
 * these proofs, we define SUBSCRIPTION_COUNT_MAX in the proof
 * Makefile.
 ****************************************************************/

// Array lists

IotMqttSubscription_t *allocate_IotMqttSubscriptionArray(IotMqttSubscription_t *pSub, size_t length);
bool valid_IotMqttSubscriptionArray(IotMqttSubscription_t *pSub, size_t length);

// Linked lists

_mqttSubscription_t *allocate_IotMqttSubscriptionListElt(_mqttSubscription_t *pElt);
bool valid_IotMqttSubscriptionListElt(_mqttSubscription_t *pElt);
IotListDouble_t *allocate_IotMqttSubscriptionList(IotListDouble_t *pSub, size_t length);
bool valid_IotMqttSubscriptionList(IotListDouble_t *pSub, size_t length);

/****************************************************************
 * IotMqttPublishInfo
 ****************************************************************/

IotMqttPublishInfo_t *allocate_IotMqttPublishInfo(IotMqttPublishInfo_t *pInfo);
bool valid_IotMqttPublishInfo(IotMqttPublishInfo_t *pInfo);

/****************************************************************
 * IotNetworkConnection
 ****************************************************************/

void *allocate_IotNetworkConnection();

/****************************************************************
 * IotNetworkInterface
 *
 * The network interface is a struct of fuction pointers that point to
 * implementions of the network API.  We define a collection of stubs
 * for these implementations that do little more that check the
 * validity of arguments and generate some minor side effects.
 *
 * The presence of these stubs can play havoc on CBMC function pointer
 * elimination.  CBMC considers all functions whose address has been
 * taken to be a candiate for the value of a function pointer.  So we
 * have to be careful not to take the address of these stubs unless we
 * have to.  In particular, we don't assign them in the allocator or
 * validator.
 *
 * Instead, when a proof requires a stub, we make an explicit
 * assumption that the needed struct member is pointing to the correct
 * stub.  The macro IS_STUBBED_NETWORKIF_XXX(IF) states that the
 * method XXX in the interface IF points to the correct stub.
 ****************************************************************/

IotNetworkInterface_t *allocate_IotNetworkInterface();
int valid_IotNetworkInterface(IotNetworkInterface_t *netif);
int stubbed_IotNetworkInterface(IotNetworkInterface_t *netif);

#define IS_STUBBED_NETWORKIF_CREATE(netif) \
  (netif->create == IotNetworkInterfaceCreate)
#define IS_STUBBED_NETWORKIF_CLOSE(netif) \
  (netif->close == IotNetworkInterfaceClose)
#define IS_STUBBED_NETWORKIF_SEND(netif) \
  (netif->send == IotNetworkInterfaceSend)
#define IS_STUBBED_NETWORKIF_RECEIVE(netif) \
  (netif->receive == IotNetworkInterfaceReceive)
#define IS_STUBBED_NETWORKIF_SETRECEIVECALLBACK(netif) \
  (netif->setReceiveCallback == IotNetworkInterfaceReceiveCallback)
#define IS_STUBBED_NETWORKIF_SETCLOSECALLBACK(netif) \
  (netif->setCloseCallback == IotNetworkInterfaceCloseCallback)
#define IS_STUBBED_NETWORKIF_DESTROY(netif) \
  (netif->destroy == IotNetworkInterfaceDestroy)

IotNetworkError_t IotNetworkInterfaceCreate( void * pConnectionInfo,
					       void * pCredentialInfo,
					       void * pConnection );
size_t IotNetworkInterfaceSend( void * pConnection,
				const uint8_t * pMessage,
				size_t messageLength );
IotNetworkError_t IotNetworkInterfaceClose( void * pConnection );
size_t IotNetworkInterfaceReceive( void * pConnection,
				   uint8_t * pBuffer,
				   size_t bytesRequested );
IotNetworkError_t IotNetworkInterfaceReceiveCallback( void * pConnection,
					       IotNetworkReceiveCallback_t
					       receiveCallback,
					       void * pContext );
IotNetworkError_t IotNetworkInterfaceCloseCallback( void * pConnection,
					       IotNetworkCloseCallback_t
					       closeCallback,
					       void * pContext );
IotNetworkError_t IotNetworkInterfaceDestroy( void * pConnection );

/****************************************************************/
