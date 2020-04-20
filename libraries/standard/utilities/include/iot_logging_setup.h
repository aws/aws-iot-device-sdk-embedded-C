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
 * When @ref LIBRARY_LOG_LEVEL is #IOT_LOG_NONE, logging is disabled and no
 * logging messages are printed.
 */
#define IOT_LOG_NONE     0

/**
 * @brief Represents erroneous application state or event.
 *
 * These messages describe the situations when a library encounters an error from
 * which it cannot recover.
 *
 * These messages are printed when @ref LIBRARY_LOG_LEVEL is defined as either
 * of #IOT_LOG_ERROR, #IOT_LOG_WARN, #IOT_LOG_INFO or #IOT_LOG_DEBUG.
 */
#define IOT_LOG_ERROR    1

/**
 * @brief Message about an abnormal event.
 *
 * These messages describe the situations when a library encounters
 * abnormal event that may be indicative of an error. Libraries continue
 * execution after logging a warning.
 *
 * These messages are printed when @ref LIBRARY_LOG_LEVEL is defined as either
 * of #IOT_LOG_WARN, #IOT_LOG_INFO or #IOT_LOG_DEBUG.
 */
#define IOT_LOG_WARN     2

/**
 * @brief A helpful, informational message.
 *
 * These messages describe normal execution of a library. They provide
 * the progress of the program at a coarse-grained level.
 *
 * These messages are printed when @ref LIBRARY_LOG_LEVEL is defined as either
 * of #IOT_LOG_INFO or #IOT_LOG_DEBUG.
 */
#define IOT_LOG_INFO     3

/**
 * @brief Detailed and excessive debug information.
 *
 * Debug log messages are used to provide the
 * progress of the program at a fine-grained level. These are mostly used
 * for debugging and may contain excessive information such as internal
 * variables, buffers, or other specific information.
 *
 * These messages are only printed when @ref LIBRARY_LOG_LEVEL is defined as
 * #IOT_LOG_DEBUG.
 */
#define IOT_LOG_DEBUG    4

/**
 * @functionpage{IotLog,logging,log}
 */

/**
 * @def IotLog( messageLevel, pLibraryName, pFormat, ... )
 * @brief The common logging interface for all libraries.
 *
 * This acts as a hook for supplying a logging implementation stack
 * for all libraries that log through this macro interface.
 * This macro should be mapped to the platform's logging library.
 *
 * @param[in] messageLevel The integer code for the log level of the message.
 * Must be one of #IOT_LOG_ERROR, #IOT_LOG_WARN, #IOT_LOG_INFO or #IOT_LOG_DEBUG.
 * Must not be #IOT_LOG_NONE.
 * @param[in] pLibraryName The string for the library name producing the
 * log message.
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
 * IotLog( IOT_LOG_ERROR, "%s" , message )
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
#else
    #if LIBRARY_LOG_LEVEL != IOT_LOG_NONE
        #if !defined( IotLog )
            #error "Please define the common logging interface macro, IotLog(messageLevel, pFormat, ...)."
        #endif
    #endif

    #if LIBRARY_LOG_LEVEL == IOT_LOG_DEBUG
        /* All log level messages will logged. */
        #define IotLogError( message )                 IotLog( IOT_LOG_ERROR, "%s", message )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( message )                  IotLog( IOT_LOG_WARN, "%s", message )
        #define IotLogWarnWithArgs( pFormat, ... )     IotLog( IOT_LOG_WARN, pFormat, __VA_ARGS__ )
        #define IotLogInfo( message )                  IotLog( IOT_LOG_INFO, "%s", message )
        #define IotLogInfoWithArgs( pFormat, ... )     IotLog( IOT_LOG_INFO, pFormat, __VA_ARGS__ )
        #define IotLogDebug( message )                 IotLog( IOT_LOG_DEBUG, "%s", message )
        #define IotLogDebugWithArgs( pFormat, ... )    IotLog( IOT_LOG_DEBUG, pFormat, __VA_ARGS__ )

    #elif LIBRARY_LOG_LEVEL == IOT_LOG_INFO
        /* Only INFO, WARNING and ERROR messages will be logged. */
        #define IotLogError( message )                 IotLog( IOT_LOG_ERROR, "%s", message )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( message )                  IotLog( IOT_LOG_WARN, "%s", message )
        #define IotLogWarnWithArgs( pFormat, ... )     IotLog( IOT_LOG_WARN, pFormat, __VA_ARGS__ )
        #define IotLogInfo( message )                  IotLog( IOT_LOG_INFO, "%s", message )
        #define IotLogInfoWithArgs( pFormat, ... )     IotLog( IOT_LOG_INFO, pFormat, __VA_ARGS__ )
        #define IotLogDebug( message )
        #define IotLogDebugWithArgs( pFormat, ... )

    #elif LIBRARY_LOG_LEVEL == IOT_LOG_WARN
        /* Only WARNING and ERROR messages will be logged.*/
        #define IotLogError( message )                 IotLog( IOT_LOG_ERROR, "%s", message )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( message )                  IotLog( IOT_LOG_WARN, "%s", message )
        #define IotLogWarnWithArgs( pFormat, ... )     IotLog( IOT_LOG_WARN, pFormat, __VA_ARGS__ )
        #define IotLogInfo( message )
        #define IotLogInfoWithArgs( pFormat, ... )
        #define IotLogDebug( message )
        #define IotLogDebugWithArgs( pFormat, ... )

    #elif LIBRARY_LOG_LEVEL == IOT_LOG_ERROR
        /* Only ERROR messages will be logged. */
        #define IotLogError( message )                 IotLog( IOT_LOG_ERROR, "%s", message )
        #define IotLogErrorWithArgs( pFormat, ... )    IotLog( IOT_LOG_ERROR, pFormat, __VA_ARGS__ )
        #define IotLogWarn( message )
        #define IotLogWarnWithArgs( pFormat, ... )
        #define IotLogInfo( message )
        #define IotLogInfoWithArgs( pFormat, ... )
        #define IotLogDebug( message )
        #define IotLogDebugWithArgs( pFormat, ... )

    #else /* if LIBRARY_LOG_LEVEL == IOT_LOG_ERROR */
        #define IotLogError( ... )
        #define IotLogWarn( ... )
        #define IotLogInfo( ... )
        #define IotLogDebug( ... )
    #endif /* if LIBRARY_LOG_LEVEL == IOT_LOG_ERROR */
#endif /* if !defined( LIBRARY_LOG_LEVEL ) || ( ( LIBRARY_LOG_LEVEL != IOT_LOG_NONE ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_ERROR ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_WARN ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_INFO ) && ( LIBRARY_LOG_LEVEL != IOT_LOG_DEBUG ) ) */

#endif /* ifndef IOT_LOGGING_SETUP_H_ */
