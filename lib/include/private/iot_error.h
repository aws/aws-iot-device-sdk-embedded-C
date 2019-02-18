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
 * @file iot_common.h
 * @brief Provides function signatures for intialization and cleanup of common
 * libraries.
 */

#ifndef _IOT_ERROR_H_
#define _IOT_ERROR_H_

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/*
 * Some macros for error standardized checking using a cleanup area.
 * This macros should not be used directly, but rather customized in the library
 * that uses them for injecting the correct library prefixes.
 */

/**
 * @brief Every public API return an enumeration value with an undelying value of 0 in case of success.
 */
#define IOT_SUCCEEDED( x )                          ( ( x ) == 0 )

/**
 * @brief Every public API returns an enumeration value with an undelying value different than 0 in case of success.
 */
#define IOT_FAILED( x )                             ( ( x ) != 0 )

/**
 * @brief Jump to the cleanup area.
 */
#define IOT_GOTO_CLEANUP()                          goto Iot_Cleanup

/**
 * @brief Just return.
 */
#define IOT_RETURN()                                return error

/**
 * @brief Declare the storage for the error status variable.
 */
#define IOT_FUNCTION_ENTRY( error_type, result )    error_type error = result

/**
 * @brief Check error and go to the cleanup area in case of failure.
 */
#define IOT_ON_ERROR_GOTO_CLEANUP( expr )           { if( IOT_FAILED( error = ( expr ) ) ) { IOT_GOTO_CLEANUP(); } }

/**
 * @brief Check error and go to the cleanup area in case of success.
 */
#define IOT_ON_SUCCESS_GOTO_CLEANUP( expr )         { if( IOT_SUCCEEDED( error = ( expr ) ) ) { IOT_GOTO_CLEANUP(); } }

/**
 * @brief Set error and go to the cleanup area.
 */
#define IOT_SET_AND_GOTO_CLEANUP( expr )            { error = ( expr ); IOT_GOTO_CLEANUP(); }

/**
 * @brief Initialize error and declare start of cleanup area.
 */

#define IOT_FUNCTION_CLEANUP( prefix )                           Iot_Cleanup :

/**
 * @brief Initialize error and declare end of cleanup area.
 */
#define IOT_FUNCTION_CLEANUP_END()                               IOT_RETURN()

/**
 * @brief Create an empty cleanup area.
 */
#define IOT_NO_FUNCTION_CLEANUP()                                IOT_FUNCTION_CLEANUP(); IOT_FUNCTION_CLEANUP_END()

/**
 * @brief Do not create a cleanup area.
 */
#define IOT_NO_FUNCTION_CLEANUP_NOLABEL( prefix )                IOT_RETURN()

/**
 * @brief Exit if the pointer is NULL.
 */
#define IOT_ON_NULL_GOTO_CLEANUP( library_prefix, ptr )          if( !( ptr ) ) IOT_SET_AND_GOTO_CLEANUP( library_prefix ## _NULL_POINTER )

/**
 * @brief Exit if an argument is NULL.
 */
#define IOT_ON_NULL_ARG_GOTO_CLEANUP( library_prefix, ptr )      if( !( ptr ) ) IOT_SET_AND_GOTO_CLEANUP( library_prefix ## _BAD_PARAMETER )

/**
 * @brief Exit if an argument is NULL.
 */
#define IOT_ON_ARG_ERROR_GOTO_CLEANUP( library_prefix, expr )    { if( IOT_FAILED( error = ( expr ) ) ) { IOT_SET_AND_GOTO_CLEANUP( library_prefix ## _BAD_PARAMETER ); } }

#endif /* ifndef _IOT_ERROR_H_ */
