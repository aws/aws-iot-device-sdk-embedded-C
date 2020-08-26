#ifndef SKIPGENERIC_H_
#define SKIPGENERIC_H_

#include <stddef.h>

typedef enum
{
    true = 1, false = 0
} bool_;

/**
 * @brief Advance buffer index beyond some minimum value.
 *
 * This function models the behavior of most of the skip* functions
 * from json.c.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] min  The smallest size required for a true result.
 *
 * @return true or false, nondeterministically
 * if true, the index in start will increment by at least min
 * but will not exceed max.
 */
bool_ skipGeneric( const char * buf,
                   size_t * start,
                   size_t max,
                   size_t min );

#endif /* ifndef SKIPGENERIC_H_ */
