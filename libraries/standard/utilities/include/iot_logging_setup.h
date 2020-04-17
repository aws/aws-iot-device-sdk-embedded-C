/*
 * IoT Common V1.1.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_logging_setup.h
 * @brief Defines the logging macro #IotLog.
 */

#ifndef IOT_LOGGING_SETUP_H_
#define IOT_LOGGING_SETUP_H_

/* The config header is always included first. */
#include "config.h"

/**
 * @constantspage{logging,logging library}
 *
 * @section logging_constants_levels Log levels
 * @brief Log levels for the libraries in this SDK.
 *
 * Each library should specify a log level by setting @ref LIBRARY_LOG_LEVEL.
 * All log messages with a level at or below the specified level will be printed
 * for that library.
 *
 * Currently, there are 4 log levels. In the order of lowest to highest, they are:
 * - #IOT_LOG_NONE <br>
 *   @copybrief IOT_LOG_NONE
 * - #IOT_LOG_ERROR <br>
 *   @copybrief IOT_LOG_ERROR
 * - #IOT_LOG_WARN <br>
 *   @copybrief IOT_LOG_WARN
 * - #IOT_LOG_INFO <br>
 *   @copybrief IOT_LOG_INFO
 * - #IOT_LOG_DEBUG <br>
 *   @copybrief IOT_LOG_DEBUG
 */

/**
 * @brief No log messages.
 *
 * Log messages with this level will be silently discarded. When @ref
 * LIBRARY_LOG_LEVEL is #IOT_LOG_NONE, logging is disabled and no [logging functions]
 * (@ref logging_functions) can be called.
 */
#define IOT_LOG_NONE     0

/**
 * @brief Only critical, unrecoverable errors.
 *
 * Log messages with this level will be printed when a library encounters an
 * error from which it cannot easily recover.
 */
#define IOT_LOG_ERROR    1

/**
 * @brief Message about an abnormal but recoverable event.
 *
 * Log messages with this level will be printed when a library encounters an
 * abnormal event that may be indicative of an error. Libraries should continue
 * execution after logging a warning.
 */
#define IOT_LOG_WARN     2

/**
 * @brief A helpful, informational message.
 *
 * Log messages with this level may indicate the normal status of a library
 * function. They should be used to track how far a program has executed.
 */
#define IOT_LOG_INFO     3

/**
 * @brief Detailed and excessive debug information.
 *
 * Log messages with this level are intended for developers. They may contain
 * excessive information such as internal variables, buffers, or other specific
 * information.
 */
#define IOT_LOG_DEBUG    4

/**
 * @functionpage{IotLog,logging,log}
 */

/**
 * @def IotLog( messageLevel, pLogConfig, ... )
 * @brief The common logging interface for all libraries.
 *
 * This acts as a hook for supplying a logging implementation stack
 * for all libraries that log with this macro interface.
 *
 * @param[in] messageLevel The integer code for the log level of the message.
 * Must be one of #IOT_LOG_ERROR, #IOT_LOG_WARN, #IOT_LOG_INFO or #IOT_LOG_DEBUG.
 * Must not be #IOT_LOG_NONE.
 * @param[in] pFormat The format string for the log message.
 * @param[in] ... The variadic argument list for the format string.
 *
 * @return No return value.
 */

/**
 * @def IotLogError( message  )
 * @brief Abbreviated logging macro for stand-alone message strings at level #IOT_LOG_ERROR.
 *
 * Equivalent to:
 * @code{c}
 * IotLogWithArgs( IOT_LOG_ERROR, "%s" , message )
 * @endcode
 */

/**
 * @def IotLogErrorWithArgs( pFormat, ...  )
 * @brief Abbreviated logging macro for messages with arguments at level #IOT_LOG_ERROR.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_ERROR, pFormat, ... )
 * @endcode
 */

/**
 * @def IotLogWarn( message  )
 * @brief Abbreviated logging macro for stand-alone message strings at level #IOT_LOG_WARN.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_WARN, "%s" , message )
 * @endcode
 */

/**
 * @def IotLogWarnWithArgs( pFormat, ...  )
 * @brief Abbreviated logging macro for messages with arguments at level #IOT_LOG_WARN.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_WARN, pFormat, ... )
 * @endcode
 */

/**
 * @def IotLogInfo( message  )
 * @brief Abbreviated logging macro for stand-alone message strings at level #IOT_LOG_INFO.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_INFO, "%s" , message )
 * @endcode
 */

/**
 * @def IotLogInfoWithArgs( pFormat, ...  )
 * @brief Abbreviated logging macro for messages with arguments at level #IOT_LOG_INFO.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_INFO, pFormat, ... )
 * @endcode
 */

/**
 * @def IotLogDebug( message  )
 * @brief Abbreviated logging macro for stand-alone message strings at level #IOT_LOG_DEBUG.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_DEBUG, "%s" , message )
 * @endcode
 */

/**
 * @def IotLogDebugWithArgs( pFormat, ...  )
 * @brief Abbreviated logging macro for messages with arguments at level #IOT_LOG_DEBUG.
 *
 * Equivalent to:
 * @code{c}
 * IotLog( IOT_LOG_DEBUG, pFormat, ... )
 * @endcode
 */

/* Check that LIBRARY_LOG_LEVEL is defined and has a valid value. */
#if !defined( LIBRARY_LOG_LEVEL ) ||           \
    ( ( LIBRARY_LOG_LEVEL != IOT_LOG_NONE ) && \
    ( LIBRARY_LOG_LEVEL != IOT_LOG_ERROR ) &&  \
    ( LIBRARY_LOG_LEVEL != IOT_LOG_WARN ) &&   \
    ( LIBRARY_LOG_LEVEL != IOT_LOG_INFO ) &&   \
    ( LIBRARY_LOG_LEVEL != IOT_LOG_DEBUG ) )
    #error "Please define LIBRARY_LOG_LEVEL as either IOT_LOG_NONE, IOT_LOG_ERROR, IOT_LOG_WARN, IOT_LOG_INFO, or IOT_LOG_DEBUG."
/* Check that LIBRARY_LOG_NAME is defined and has a valid value. */
#elif !defined( LIBRARY_LOG_NAME )
    #error "Please define LIBRARY_LOG_NAME."
#else
    #if LIBRARY_LOG_LEVEL != IOT_LOG_NONE
        #if !defined( IotLog )
            #error "Please define the common logging interface macro, IotLog(messageLevel, pFormat, ...)."
        #endif
    #endif

    #if LIBRARY_LOG_LEVEL == IOT_LOG_DEBUG
        /* All log levels will logged. */
        #define IotLogError( pFormat )                 IotLog( IOT_LOG_ERROR, "%s", pFormat )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( pFormat )                  IotLog( IOT_LOG_WARN, "%s", pFormat )
        #define IotLogWarnWithArgs( pFormat, ... )     IotLog( IOT_LOG_WARN, pFormat, __VA_ARGS__ )
        #define IotLogInfo( pFormat )                  IotLog( IOT_LOG_INFO, "%s", pFormat )
        #define IotLogInfoWithArgs( pFormat, ... )     IotLog( IOT_LOG_INFO, pFormat, __VA_ARGS__ )
        #define IotLogDebug( pFormat )                 IotLog( IOT_LOG_DEBUG, "%s", pFormat )
        #define IotLogDebugWithArgs( pFormat, ... )    IotLog( IOT_LOG_DEBUG, pFormat, __VA_ARGS__ )

/* If log level is DEBUG, enable the function to print buffers. */
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize ) \
    IotLog_GenericPrintBuffer( LIBRARY_LOG_NAME,                   \
                               pHeader,                            \
                               pBuffer,                            \
                               bufferSize )
        /* Remove references to IotLog from the source code if logging is disabled. */
    #elif LIBRARY_LOG_LEVEL == IOT_LOG_INFO
        /* Debug messages will not be logged. All other macros will call IotLog */
        #define IotLogError( pFormat )                 IotLog( IOT_LOG_ERROR, "%s", pFormat )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( pFormat )                  IotLog( IOT_LOG_WARN, "%s", pFormat )
        #define IotLogWarnWithArgs( pFormat, ... )     IotLog( IOT_LOG_WARN, pFormat, __VA_ARGS__ )
        #define IotLogInfo( pFormat )                  IotLog( IOT_LOG_INFO, "%s", pFormat )
        #define IotLogInfoWithArgs( pFormat, ... )     IotLog( IOT_LOG_INFO, pFormat, __VA_ARGS__ )
        #define IotLogDebug( pFormat )
        #define IotLogDebugWithArgs( pFormat, ... )
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
    #elif LIBRARY_LOG_LEVEL == IOT_LOG_WARN
        /* Only "Warning" and IOT_LOG_ERROR messages will be logged.*/
        #define IotLogError( pFormat )                 IotLog( IOT_LOG_ERROR, "%s", pFormat )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( pFormat )                  IotLog( IOT_LOG_WARN, "%s", pFormat )
        #define IotLogWarnWithArgs( pFormat, ... )     IotLog( IOT_LOG_WARN, pFormat, __VA_ARGS__ )
        #define IotLogInfo( pFormat )
        #define IotLogInfoWithArgs( pFormat, ... )
        #define IotLogDebug( pFormat )
        #define IotLogDebugWithArgs( pFormat, ... )
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
    #elif LIBRARY_LOG_LEVEL == IOT_LOG_ERROR
        /* Only IOT_LOG_ERROR messages will be logged. */
        #define IotLogError( pFormat )                 IotLog( IOT_LOG_ERROR, "%s", pFormat )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( pFormat )
        #define IotLogWarnWithArgs( pFormat, ... )
        #define IotLogInfo( pFormat )
        #define IotLogInfoWithArgs( pFormat, ... )
        #define IotLogDebug( pFormat )
        #define IotLogDebugWithArgs( pFormat, ... )
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
    #else /* if LIBRARY_LOG_LEVEL >= IOT_LOG_DEBUG */
        /* @[declare_logging_printbuffer] */
        #define IotLog_PrintBuffer( pHeader, pBuffer, bufferSize )
        /* @[declare_logging_printbuffer] */
        #define IotLogError( ... )
        #define IotLogWarn( ... )
        #define IotLogInfo( ... )
        #define IotLogDebug( ... )
    #endif /* if LIBRARY_LOG_LEVEL >= IOT_LOG_DEBUG */
#endif /* if !defined( LIBRARY_LOG_LEVEL ) || ( ( LIBRARY_LOG_LEVEL != IOT_LOG_NONE ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_ERROR ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_WARN ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_INFO ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_DEBUG ) ) */

#endif /* ifndef IOT_LOGGING_SETUP_H_ */
