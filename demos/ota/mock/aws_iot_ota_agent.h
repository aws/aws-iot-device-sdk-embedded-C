#ifndef AWS_IOT_OTA_AGENT_H
#define AWS_IOT_OTA_AGENT_H

#include <stdint.h>

#define kOTA_Err_None                    0x00000000UL
#define kOTA_Err_Uninitialized           0xff000000UL

typedef enum
{
    eOTA_AgentState_Suspended,
    eOTA_AgentState_Stopped
} OTA_State_t;

typedef enum
{
    eOTA_ImageState_Unknown = 0,
    eOTA_ImageState_Testing = 1,
    eOTA_ImageState_Accepted = 2,
    eOTA_ImageState_Rejected = 3,
    eOTA_ImageState_Aborted = 4,
    eOTA_LastImageState = eOTA_ImageState_Aborted
} OTA_ImageState_t;

typedef enum
{
    eOTA_JobEvent_Activate = 0,
    eOTA_JobEvent_Fail,
    eOTA_JobEvent_StartTest,
    eOTA_LastJobEvent = eOTA_JobEvent_StartTest
} OTA_JobEvent_t;

typedef uint32_t OTA_Err_t;

typedef void (* pxOTACompleteCallback_t)( OTA_JobEvent_t eEvent );

OTA_State_t OTA_AgentInit( void * pvConnectionContext,
                           const uint8_t * pucThingName,
                           pxOTACompleteCallback_t xFunc,
                           uint32_t xTicksToWait ) { return 0; }
OTA_State_t OTA_AgentShutdown( uint32_t xTicksToWait ) { return 0; }
OTA_State_t OTA_GetAgentState( void ) { return 0; }
const char * OTA_GetAgentStateStr( void ) { return ""; }
OTA_Err_t OTA_ActivateNewImage( void ) { return 0; }
OTA_Err_t OTA_SetImageState( OTA_ImageState_t eState ) { return 0; }
OTA_ImageState_t OTA_GetImageState( void ) { return 0; }
OTA_Err_t OTA_CheckForUpdate( void ) { return 0; }
OTA_Err_t OTA_Suspend( void ) { return 0; }
OTA_Err_t OTA_Resume( void * pxConnection ) { return 0; }

uint32_t OTA_GetPacketsReceived( void ) { return 0; }
uint32_t OTA_GetPacketsQueued( void ) { return 0; }
uint32_t OTA_GetPacketsProcessed( void ) { return 0; }
uint32_t OTA_GetPacketsDropped( void ) { return 0; }

#endif
