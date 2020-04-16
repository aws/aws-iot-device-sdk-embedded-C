/*
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

#ifndef CONFIG_H
#define CONFIG_H

/* Set network context to socket (int). */
typedef int MQTTNetworkContext_t;

#define MQTT_MAX_QUEUED_PUBLISH_MESSAGES 10

/*
 * @brief The Logging Interface Hook.
 * 
 * @note Customers can EITHER
 * Define this macro to tie with their logging
 * stack. 
 *          OR
 * Use the reference POSIX implementation, IotLog_Generic provided by us.
 * 
 * @param[in] messageLevel The integer logging level code for the message.
 * @param[in] pFormat The format string for the log message.
 * @param[in] ... The variadic argument list for the format string.
 **/
#define IotLog( messageLevel, pFormat, ... )

#endif
