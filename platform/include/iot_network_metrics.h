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
 * @file iot_network_metrics.h
 * @brief Declares the network stack functions with Device Defender metrics.
 *
 * This file does not provide a different networking implementation; it only wraps
 * existing network implementations with the necessary metrics functions.
 */

#ifndef IOT_NETWORK_METRICS_H_
#define IOT_NETWORK_METRICS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Platform metrics header. */
#include "platform/iot_metrics.h"

/* Platform network include. */
#include "platform/iot_network.h"

/**
 * @brief Provides a pointer to an #IotNetworkInterface_t that uses that provides
 * metrics.
 */
#define IOT_NETWORK_INTERFACE_METRICS    ( &( IotNetworkMetrics ) )

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Declaration of a network interface struct with metrics.
 */
extern const IotNetworkInterface_t IotNetworkMetrics;
/** @endcond */

#endif /* ifndef IOT_NETWORK_METRICS_H_ */
