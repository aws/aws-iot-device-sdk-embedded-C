#ifndef HTTP_CBMC_STATE_H_
#define HTTP_CBMC_STATE_H_

#include "http_client.h"

/**
 * @brief Calls malloc based on given size but also returns NULL for coverage.
 *
 * Implementation of safe malloc which returns NULL if the requested size is 0.
 *
 * @note Warning: The behavior of malloc(0) is platform dependent.
 * It is possible for malloc(0) to return an address without allocating memory.
 */
void * safeMalloc( size_t xWantedSize );

/**
 * @brief Allocate a request headers object.
 */
HTTPRequestHeaders_t * allocateHttpRequestHeaders();

/**
 * @brief Returns true if a request headers object is feasible.
 */
int isValidHttpRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders );

#endif /* ifndef HTTP_CBMC_STATE_H_ */
