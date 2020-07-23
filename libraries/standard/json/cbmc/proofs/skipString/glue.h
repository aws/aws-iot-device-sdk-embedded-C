#ifndef GLUE_H_
#define GLUE_H_

#include "skipGeneric.h"

bool_ skipEscape( const char * buf,
                  size_t * start,
                  size_t max );

bool_ skipUTF8( const char * buf,
                size_t * start,
                size_t max );

bool_ skipString( const char * buf,
                  size_t * start,
                  size_t max );

#endif /* ifndef GLUE_H_ */
