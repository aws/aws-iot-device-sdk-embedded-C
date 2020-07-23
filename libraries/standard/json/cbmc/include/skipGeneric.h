#ifndef SKIPGENERIC_H_
#define SKIPGENERIC_H_

#include <stddef.h>

typedef enum
{
    true = 1, false = 0
} bool_;

bool_ skipGeneric( const char * buf,
                   size_t * start,
                   size_t max,
                   size_t min );

#endif /* ifndef SKIPGENERIC_H_ */
