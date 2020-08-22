#ifndef CLOSE_H_
#define CLOSE_H_

/**
 * @file close.h
 * @brief This file is used to generate a mock for close(int fd) since mocking
 * unistd.h itself causes several compilation errors from parsing its macros.
 */

/* Close the file descriptor FD.
 *
 * This function is a cancellation point and therefore not marked with
 * __THROW.  */
extern int close( int __fd );

#endif
