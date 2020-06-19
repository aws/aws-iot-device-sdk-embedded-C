#ifndef HTTP_CBMC_STATE_H_
#define HTTP_CBMC_STATE_H_

#include "http_client.h"

HTTPRequestHeaders_t * allocate_HTTPRequestHeaders();
int is_valid_HTTPRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders );

#endif /* ifndef HTTP_CBMC_STATE_H_ */
