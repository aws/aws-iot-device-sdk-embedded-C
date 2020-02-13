#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

/****************************************************************
 * Stub out RemoveAllMatches.
 *
 * The only invocation of RemoveAllMatches in DeserializeSuback is to
 * remove subscriptions from the connection's subscription list.  This
 * stub abstracts RemoveAllMatches by replacing the list with an
 * unconstrained list of subscriptions.  We don't even bother to fill
 * in the topic subscription filters.  By design, any actual use of
 * the list in subsequent code (there is none) will trigger pointer
 * errors.
/****************************************************************/

void IotListDouble_RemoveAllMatches( const IotListDouble_t * const pList,
				     bool ( *isMatch )( const IotLink_t * const pOperationLink,
							void * pCompare ),
				     void * pMatch,
				     void ( *freeElement )( void * pData ),
				     size_t linkOffset )
{
  IotListDouble_t *sentinal = pList->pNext->pPrevious;

  size_t num_elts;
  __CPROVER_assume(num_elts < SUBSCRIPTION_COUNT_MAX);

  // Allocate lists of length at most 3
  __CPROVER_assert(SUBSCRIPTION_COUNT_MAX <= 4,
		   "Subscription lists limited to 3 elements");

  if (1 <= num_elts)
    {
      _mqttSubscription_t *pElt = malloc(sizeof(*pElt));
      sentinal->pNext = &pElt->link;
      pElt->link.pPrevious = sentinal;
      pElt->link.pNext = sentinal;
      sentinal->pPrevious = &pElt->link;
    }
  if (2 <= num_elts)
    {
      _mqttSubscription_t *pElt = malloc(sizeof(*pElt));
      sentinal->pNext = &pElt->link;
      pElt->link.pPrevious = sentinal;
      pElt->link.pNext = sentinal;
      sentinal->pPrevious = &pElt->link;
    }
  if (3 <= num_elts)
    {
      _mqttSubscription_t *pElt = malloc(sizeof(*pElt));
      sentinal->pNext = &pElt->link;
      pElt->link.pPrevious = sentinal;
      pElt->link.pNext = sentinal;
      sentinal->pPrevious = &pElt->link;
    }
}

/****************************************************************
 * Proof harness
 ****************************************************************/

void harness()
{
    _mqttPacket_t suback;

    // Create packet data
    __CPROVER_assume( suback.remainingLength <= BUFFER_SIZE );
    suback.pRemainingData = malloc( sizeof( uint8_t )
				    * suback.remainingLength );

    // Create packet connection
    IotMqttConnection_t pConn = allocate_IotMqttConnection(NULL);
    __CPROVER_assume(pConn);
    ensure_IotMqttConnection_has_lists(pConn);
    __CPROVER_assume(valid_IotMqttConnection(pConn));
    suback.u.pMqttConnection = pConn;

    // Argument must be a nonnull pointer
    _IotMqtt_DeserializeSuback( &suback );
}

/****************************************************************/
