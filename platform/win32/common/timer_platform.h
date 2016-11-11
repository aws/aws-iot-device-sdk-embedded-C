/*
* Copyright 2010-2015 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#ifndef _TIMER_PLATFORM_H_
#define _TIMER_PLATFORM_H_

#include <Windows.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
	LARGE_INTEGER endTime;
} Timer;

extern bool has_timer_expired(Timer *timer);
extern void countdown_ms(Timer *timer, unsigned __int32 timeout);
extern void countdown_sec(Timer *timer, unsigned __int32 timeout);
extern unsigned __int32 left_ms(Timer *timer);
extern void init_timer(Timer *timer);

#ifdef __cplusplus
}
#endif

#endif /* _TIMER_PLATFORM_H_ */
