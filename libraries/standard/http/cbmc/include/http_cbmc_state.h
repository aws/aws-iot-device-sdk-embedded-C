#ifndef HTTP_CBMC_STATE_H_
#define HTTP_CBMC_STATE_H_

#include "http_client.h"

/* Implementation of safe malloc which returns NULL if the requested
 * size is 0.  Warning: The behavior of malloc(0) is platform
 * dependent.  It is possible for malloc(0) to return an address
 * without allocating memory.
 */
void * safeMalloc( size_t xWantedSize );
HTTPRequestHeaders_t * allocateHTTPRequestHeaders();
int isValidHTTPRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders );

#endif /* ifndef HTTP_CBMC_STATE_H_ */
