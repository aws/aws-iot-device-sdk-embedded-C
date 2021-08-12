/*
 * SigV4 Utility Library v1.0.0
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
 * @file sigv4_config.h
 * @brief Values for configuration macros provided by the application to be
 * used by the SigV4 Utility Library.
 */

#ifndef SIGV4_CONFIG_H_
#define SIGV4_CONFIG_H_

/**
 * @brief Macro defining the size of the internal buffer used for incremental
 * canonicalization and hashing.
 *
 * A buffer of this size in bytes is declared on the stack. It should be be
 * large enough for the digest output of the specified hash function.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `1024`
 */
#ifndef SIGV4_PROCESSING_BUFFER_LENGTH
    #define SIGV4_PROCESSING_BUFFER_LENGTH    1024U
#endif

/**
 * @brief Macro defining the maximum number of headers in the request, used to
 * assist the library in sorting header fields during canonicalization.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `100`
 */
#ifndef SIGV4_MAX_HTTP_HEADER_COUNT
    #define SIGV4_MAX_HTTP_HEADER_COUNT    100U
#endif

/**
 * @brief Macro defining the maximum number of query key/value pairs, used to
 * assist the library in sorting query keys during canonicalization.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `100`
 */
#ifndef SIGV4_MAX_QUERY_PAIR_COUNT
    #define SIGV4_MAX_QUERY_PAIR_COUNT    100U
#endif

/**
 * @brief Macro indicating the largest block size of any hashing
 * algorithm used for SigV4 authentication i.e. the maximum of all
 * values specified for the hashBlockLen in #SigV4CryptoInterface_t.
 * For example, using SHA-512 would require this value to be at least 128.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `64`
 */
#ifndef SIGV4_HASH_MAX_BLOCK_LENGTH
    #define SIGV4_HASH_MAX_BLOCK_LENGTH    64U
#endif

/**
 * @brief Macro defining the maximum digest length of the specified hash function,
 * used to determine the length of the output buffer.
 *
 * This macro should be updated if using a hashing algorithm other than SHA256
 * (32 byte digest length). For example, using SHA512 would require this
 * value to be at least 64.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `32`
 */
#ifndef SIGV4_HASH_MAX_DIGEST_LENGTH
    #define SIGV4_HASH_MAX_DIGEST_LENGTH    32U
#endif

/**
 * @brief Macro to statically enable support for canonicalizing the URI,
 * headers, and query in this utility.
 *
 * Set this to one to enable the encoding functions used to create the canonical
 * request.
 *
 * <b>Possible values:</b> 0 or 1 <br>
 * <b>Default value:</b> `1`
 */
#ifndef SIGV4_USE_CANONICAL_SUPPORT
    #define SIGV4_USE_CANONICAL_SUPPORT    1
#endif

/**
 * @brief Macro called by the SigV4 Utility library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the SigV4 Utility library, this macro should
 * be mapped to the application-specific logging implementation that supports
 * error logging.
 *
 * @note This logging macro is called in the SigV4 Utility library with
 * parameters wrapped in double parentheses to be ISO C89/C90 standard
 * compliant. For a reference POSIX implementation of the logging macros, refer
 * to sigv4_config.h files, and the logging-stack in demos folder of the [AWS
 * IoT Embedded C SDK
 * repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated
 * for calls to the macro in the SigV4 Utility library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro called by the the SigV4 Utility library for logging "Warning"
 * level messages.
 *
 * To enable warning level logging in the SigV4 Utility library, this macro
 * should be mapped to the application-specific logging implementation that
 * supports warning logging.
 *
 * @note This logging macro is called in the SigV4 Utility library with
 * parameters wrapped in double parentheses to be ISO C89/C90 standard
 * compliant. For a reference POSIX implementation of the logging macros, refer
 * to sigv4_config.h files, and the logging-stack in demos folder of the [AWS
 * IoT Embedded C SDK
 * repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Warning logs are turned off, and no code is generated
 * for calls to the macro in the SigV4 Utility library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro called by the the SigV4 Utility library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the SigV4 Utility library, this macro should
 * be mapped to the application-specific logging implementation that supports
 * info logging.
 *
 * @note This logging macro is called in the SigV4 Utility library with
 * parameters wrapped in double parentheses to be ISO C89/C90 standard
 * compliant. For a reference POSIX implementation of the logging macros, refer
 * to sigv4_config.h files, and the logging-stack in demos folder of the [AWS
 * IoT Embedded C SDK
 * repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is generated
 * for calls to the macro in the SigV4 Utility library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro called by the the SigV4 Utility library for logging "Debug"
 * level messages.
 *
 * To enable debug level logging from SigV4 Utility library, this macro should
 * be mapped to the application-specific logging implementation that supports
 * debug logging.
 *
 * @note This logging macro is called in the SigV4 Utility library with
 * parameters wrapped in double parentheses to be ISO C89/C90 standard
 * compliant. For a reference POSIX implementation of the logging macros, refer
 * to sigv4_config.h files, and the logging-stack in demos folder of the [AWS
 * IoT Embedded C SDK
 * repository](https://github.com/aws/aws-iot-device-sdk-embedded-C).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is generated
 * for calls to the macro in the SigV4 Utility library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef SIGV4_CONFIG_H_ */
