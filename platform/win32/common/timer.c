/*
* Copyright 2010-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
*
* Licensed under the Apache License, Version 2.0 (the "License").
* You may not use this file except in compliance with the License.
* A copy of the License is located at
*
*  http://aws.amazon.com/apache2.0
*
* or in the "license" file accompanying this file. This file is distributed
* on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
* express or implied. See the License for the specific language governing
* permissions and limitations under the License.
*/

#ifdef __cplusplus
extern "C" {
#endif

#include "timer_platform.h"

// Timeout if 'now' greater than 'endTime'
bool has_timer_expired(Timer *timer) 
{	
	LARGE_INTEGER now;
	QueryPerformanceCounter(&now);

	return (now.QuadPart > timer->endTime.QuadPart);
}

// Calculate a new 'endTime' given the 'timeout' passed in by the client
// TODO:: Check for timer rollover.
void countdown_ms(Timer *timer, unsigned __int32 timeout) 
{
	LARGE_INTEGER freq, now;
	QueryPerformanceFrequency(&freq);

	// Convert 'timeout' to ticks
	LARGE_INTEGER timeoutTicks;
	timeoutTicks.QuadPart = (timeout * freq.QuadPart) / 1000LL;
	
	// Calculate 'endTime' 
	QueryPerformanceCounter(&now);
	timer->endTime.QuadPart = now.QuadPart + timeoutTicks.QuadPart;
}

unsigned __int32 left_ms(Timer *timer) 
{
	_int32 leftMilliseconds = 0;

	LARGE_INTEGER now;
	QueryPerformanceCounter(&now);

	LONGLONG delta = timer->endTime.QuadPart - now.QuadPart;
	if (delta > 0)
	{
		LARGE_INTEGER freq;
		QueryPerformanceFrequency(&freq);
		leftMilliseconds = (__int32)((1000LL * delta) / freq.QuadPart);
	}
	
	return leftMilliseconds;
}

void countdown_sec(Timer *timer, unsigned __int32 timeout) 
{
	countdown_ms(timer, timeout * 1000);
}

void init_timer(Timer *timer) 
{	
	timer->endTime.QuadPart = 0LL;
}

#ifdef __cplusplus
}
#endif
