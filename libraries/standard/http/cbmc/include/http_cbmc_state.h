#ifndef HTTP_CBMC_STATE_H_
#define HTTP_CBMC_STATE_H_

#include "http_client.h"

/**
 * @brief Calls malloc based on given size or returns NULL for coverage.
 *
 * Implementation of safe malloc which returns NULL if the requested size is 0.
 * The behavior of malloc(0) is platform dependent.
 * It is possible for malloc(0) to return an address without allocating memory.
 *
 * @brief param[in] wantedSize Requested size to malloc.
 */
void * safeMalloc( size_t wantedSize );

/**
 * @brief Allocate a request headers object.
 */
HTTPRequestHeaders_t * allocateHttpRequestHeaders();

/**
 * @brief Validates if a request headers object is feasible.
 *
 * @brief param[in] pRequestHeaders Request headers to validate.
 *
 * @return 1 if request headers is feasible; 0 otherwise.
 */
int isValidHttpRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders );

#endif /* ifndef HTTP_CBMC_STATE_H_ */
