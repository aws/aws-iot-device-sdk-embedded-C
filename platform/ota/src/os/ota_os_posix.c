/*
 * FreeRTOS OTA V1.2.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* Standard Includes.*/
#include <string.h>
#include <sys/time.h>
#include <sys/types.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>
#include <mqueue.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* OTA OS Interface Includes.*/
#include "ota_os_interface.h"

/* OTA OS POSIX Interface Includes.*/
#include "ota_os_posix.h"

/* OTA Event queue attributes.*/
#define OTA_QUEUE_NAME   "/otaqueue"
#define QUEUE_PERMISSIONS 0777
#define MAX_MESSAGES 10
#define MAX_MSG_SIZE 12

/* OTA Event queue attributes.*/
static mqd_t otaEventQueue;

int32_t ota_InitEvent( OtaEventContext_t* pContext )
{
    (void) pContext;
    struct mq_attr attr;

    /* Initialize the attributes.*/
    attr.mq_flags = 0;
    attr.mq_maxmsg = MAX_MESSAGES;
    attr.mq_msgsize = MAX_MSG_SIZE;
    attr.mq_curmsgs = 0;

    /* Open the OTA event queue .*/
    if ( ( otaEventQueue = mq_open ( OTA_QUEUE_NAME, O_CREAT | O_RDWR, QUEUE_PERMISSIONS, &attr ) ) == -1 )
    {
        LogInfo( (  "OTA Event Queue created." ) );

        /* This is fatal error , exit the application */
        exit ( 1 );
    }

    return 0;
}

int32_t ota_SendEvent( OtaEventContext_t* pContext,
                       const void* pEventMsg,
                       unsigned int timeout)
{

    (void) pContext;
    (void) timeout;

    /* Send the event to OTA event queue.*/
    if ( mq_send ( otaEventQueue, pEventMsg, MAX_MSG_SIZE, 0 ) == -1)
    {
        LogInfo( (  "OTA Event Sent." ) );
        exit (1);

    }else
    {
        LogDebug ( ( "OTA Event Queue busy." ) );
        return 0;
    }

}

int32_t ota_ReceiveEvent( OtaEventContext_t* pContext,
                          void* pEventMsg,
                          uint32_t timeout)
{
    (void) pContext;
    (void) timeout;

    char buff[MAX_MSG_SIZE];

    /* Delay a bit.*/
    sleep(1);

        if ( mq_receive ( otaEventQueue, buff, sizeof(buff), NULL) == -1 )
        {
            LogInfo( (  "OTA Event receive fatal error." ) );
            exit (1);
        }
        else
        {
            LogInfo( (  "OTA Event received" ) );

            /* copy the data from local buffer.*/
            memcpy( pEventMsg, buff, MAX_MSG_SIZE );
            return 1;
        }
    return 0;
}

void ota_DeinitEvent( OtaEventContext_t* pContext )
{
  (void) pContext;

  /* Remove the event queue.*/
  mq_unlink( OTA_QUEUE_NAME );
}
