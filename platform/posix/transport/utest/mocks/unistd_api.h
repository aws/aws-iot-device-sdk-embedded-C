#ifndef UNISTD_API_H_
#define UNISTD_API_H_

/**
 * @file unistd_api.h
 * @brief This file is used to generate a mock for any functions from
 * unistd.h since mocking unistd.h causes several compilation errors from
 * parsing its macros.
 */

/* Close the file descriptor FD.
 *
 * This function is a cancellation point and therefore not marked with
 * __THROW.  */
extern int close( int __fd );

/* Get the pathname of the current working directory,
 * and put it in SIZE bytes of BUF.  Returns NULL if the
 * directory couldn't be determined or SIZE was too small.
 * If successful, returns BUF.  In GNU, if BUF is NULL,
 * an array is allocated with `malloc'; the array is SIZE
 * bytes long, unless SIZE == 0, in which case it is as
 * big as necessary.  */
extern char * getcwd( char * __buf,
                      size_t __size );

#endif /* ifndef UNISTD_API_H_ */
