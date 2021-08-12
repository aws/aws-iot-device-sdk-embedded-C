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

#ifndef SIGV4_PROCESSING_BUFFER_LENGTH
    #define SIGV4_PROCESSING_BUFFER_LENGTH    1024U
#endif

#ifndef SIGV4_MAX_HTTP_HEADER_COUNT
    #define SIGV4_MAX_HTTP_HEADER_COUNT    100U
#endif

#ifndef SIGV4_MAX_QUERY_PAIR_COUNT
    #define SIGV4_MAX_QUERY_PAIR_COUNT    100U
#endif

#ifndef SIGV4_HASH_MAX_BLOCK_LENGTH
    #define SIGV4_HASH_MAX_BLOCK_LENGTH    64U
#endif

#ifndef SIGV4_HASH_MAX_DIGEST_LENGTH
    #define SIGV4_HASH_MAX_DIGEST_LENGTH    32U
#endif

#ifndef SIGV4_USE_CANONICAL_SUPPORT
    #define SIGV4_USE_CANONICAL_SUPPORT    1
#endif

/* Logging configuration for the SigV4 library. */
#ifndef LogError
    #define LogError( message )
#endif

#ifndef LogWarn
    #define LogWarn( message )
#endif

#ifndef LogInfo
    #define LogInfo( message )
#endif

#ifndef LogDebug
    #define LogDebug( message )
#endif

#endif /* ifndef SIGV4_CONFIG_H_ */
