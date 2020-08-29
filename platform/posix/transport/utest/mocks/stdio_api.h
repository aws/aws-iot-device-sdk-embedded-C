#ifndef STDIO_API_H_
#define STDIO_API_H_

#include <stdio.h>

/**
 * @file stdio_api.h
 * @brief This file is used to generate mocks for functions used from <stdio.h>.
 * Mocking stdio.h itself causes several errors from parsing its macros.
 */

/* Open a file and create a new stream for it. */
extern _IO_FILE * fopen( const char * __filename,
                         const char * __modes );

/* Close STREAM. */
extern int fclose( _IO_FILE * __stream );

#endif /* ifndef STDIO_API_H_ */
