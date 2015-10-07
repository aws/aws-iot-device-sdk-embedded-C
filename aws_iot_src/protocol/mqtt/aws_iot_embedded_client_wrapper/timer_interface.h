/*******************************************************************************
 * Copyright (c) 2014 IBM Corp.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * and Eclipse Distribution License v1.0 which accompany this distribution.
 *
 * The Eclipse Public License is available at
 *    http://www.eclipse.org/legal/epl-v10.html
 * and the Eclipse Distribution License is available at
 *   http://www.eclipse.org/org/documents/edl-v10.php.
 *
 * Contributors:
 *    Allan Stockdill-Mander - initial API and implementation and/or initial documentation
 *******************************************************************************/

/**
 * @file timer_interface.h
 * @brief Timer interface definition for MQTT client.
 *
 * Defines an interface to timers that can be used by other system
 * components.  MQTT client requires timers to handle timeouts and
 * MQTT keep alive.
 * Starting point for porting the SDK to the timer hardware layer of a new platform.
 */

#ifndef __TIMER_INTERFACE_H_
#define __TIMER_INTERFACE_H_

// Add the platform specific timer includes to define the Timer struct
#include "timer_linux.h"

/**
 * @brief Timer Type
 *
 * Forward declaration of a timer struct.  The definition of this struct is
 * platform dependent.  When porting to a new platform add this definition
 * in "timer_<platform>.h" and include that file above.
 *
 */
typedef struct Timer Timer;

/**
 * @brief Check if a timer is expired
 *
 * Call this function passing in a timer to check if that timer has expired.
 *
 * @param Timer - pointer to the timer to be checked for expiration
 * @return character - 1 = timer expired, 0 = timer not expired
 */
char expired(Timer*);

/**
 * @brief Create a timer (milliseconds)
 *
 * Sets the timer to expire in a specified number of milliseconds.
 *
 * @param Timer - pointer to the timer to be set to expire in milliseconds
 * @param unsigned int - set the timer to expire in this number of milliseconds
 */
void countdown_ms(Timer*, unsigned int);

/**
 * @brief Create a timer (seconds)
 *
 * Sets the timer to expire in a specified number of seconds.
 *
 * @param Timer - pointer to the timer to be set to expire in seconds
 * @param unsigned int - set the timer to expire in this number of seconds
 */
void countdown(Timer*, unsigned int);

/**
 * @brief Check the time remaining on a give timer
 *
 * Checks the input timer and returns the number of milliseconds remaining on the timer.
 *
 * @param Timer - pointer to the timer to be set to checked
 * @return int - milliseconds left on the countdown timer
 */
int left_ms(Timer*);

/**
 * @brief Initialize a timer
 *
 * Performs any initialization required to the timer passed in.
 *
 * @param Timer - pointer to the timer to be initialized
 */
void InitTimer(Timer*);

#endif //__TIMER_INTERFACE_H_
