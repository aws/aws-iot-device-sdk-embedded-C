#ifndef GLUE_H_
#define GLUE_H_

#include "json.h"
#include "skipGeneric.h"

bool_ skipAnyScalar( const char * buf,
                     size_t * start,
                     size_t max );

JSONStatus_t skipCollection( const char * buf,
                             size_t * start,
                             size_t max );

void skipSpace( const char * buf,
                size_t * start,
                size_t max );

bool_ skipSpaceAndComma( const char * buf,
                         size_t * start,
                         size_t max );

bool_ skipString( const char * buf,
                  size_t * start,
                  size_t max );

#endif /* ifndef GLUE_H_ */
