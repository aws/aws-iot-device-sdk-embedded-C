/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file iot_clock_template.c
 * @brief Template implementation of the functions in iot_clock.h
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Platform clock include. */
#include "platform/iot_clock.h"

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_PLATFORM
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_PLATFORM
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "CLOCK" )
#include "iot_logging_setup.h"

/*-----------------------------------------------------------*/

bool IotClock_GetTimestring( char * pBuffer,
                             size_t bufferSize,
                             size_t * pTimestringLength )
{
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_clock_function_gettimestring.html
     */
    return false;
}

/*-----------------------------------------------------------*/

uint64_t IotClock_GetTimeMs( void )
{
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_clock_function_gettimems.html
     */
    return 0;
}

/*-----------------------------------------------------------*/

void IotClock_SleepMs( uint32_t sleepTimeMs )
{
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_clock_function_sleepms.html
     */
}

/*-----------------------------------------------------------*/

bool IotClock_TimerCreate( IotTimer_t * pNewTimer,
                           IotThreadRoutine_t expirationRoutine,
                           void * pArgument )
{
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_clock_function_timercreate.html
     */
    return false;
}

/*-----------------------------------------------------------*/

void IotClock_TimerDestroy( IotTimer_t * pTimer )
{
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_clock_function_timerdestroy.html
     */
}

/*-----------------------------------------------------------*/

bool IotClock_TimerArm( IotTimer_t * pTimer,
                        uint32_t relativeTimeoutMs,
                        uint32_t periodMs )
{
    /* Implement this function as specified here:
     * https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/platform_clock_function_timerarm.html
     */
    return false;
}

/*-----------------------------------------------------------*/
