#ifndef TIME_API_H_
#define TIME_API_H_

/**
 * @file time_api.h
 * @brief This file is used to generate a mock for any functions from
 * time.h since mocking time.h causes several compilation errors from
 * parsing its macros.
 */

/* Make the process sleep for SECONDS seconds, or until a signal arrives
 * and is not ignored.  The function returns the number of seconds less
 * than SECONDS which it actually slept (thus zero if it slept the full time).
 * If a signal handler does a `longjmp' or modifies the handling of the
 * SIGALRM signal while inside `sleep' call, the handling of the SIGALRM
 * signal afterwards is undefined.  There is no return value to indicate
 * error, but if `sleep' returns SECONDS, it probably didn't work.
 *
 * This function is a cancellation point and therefore not marked with
 * __THROW.  */
extern unsigned int sleep( unsigned int seconds );

#endif /* ifndef TIME_API_H_ */
