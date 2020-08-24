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

/**
 * @file MQTT_MatchTopic_harness.c
 * @brief Implements the proof harness for MQTT_MatchTopic function.
 */

#include "mqtt.h"
#include "mqtt_cbmc_state.h"

void harness()
{
    const char * pTopicName;
    uint16_t nameLength;
    const char * pTopicFilter;
    uint16_t filterLength;
    bool * pMatchResult;

    __CPROVER_assume( nameLength < MAX_TOPIC_NAME_FILTER_LENGTH );
    pTopicName = mallocCanFail( ( sizeof( char ) * nameLength ) );
    __CPROVER_assume( filterLength < MAX_TOPIC_NAME_FILTER_LENGTH );
    pTopicFilter = mallocCanFail( ( sizeof( char ) * filterLength ) );
    pMatchResult = mallocCanFail( sizeof( bool ) );

    MQTT_MatchTopic( pTopicName,
                     nameLength,
                     pTopicFilter,
                     filterLength,
                     pMatchResult );
}
