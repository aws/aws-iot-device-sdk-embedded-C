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
 * @file iot_tests.c
 * @brief Common test runner.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Error handling include. */
#include "private/iot_error.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Test framework includes. */
#include "unity_fixture.h"

/*-----------------------------------------------------------*/

/* This file calls a generic placeholder test runner function. The build system selects
 * the actual function by defining it. When testing demos applications, the demo main
 * function is called. */
#if IOT_TEST_DEMO == 1
    extern int DemoMain( int argc,
                         char ** argv );

#else
    extern void RunTests( bool disableNetworkTests,
                          bool disableLongTests );
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Used to provide unity_malloc with critical sections.
 */
static IotMutex_t _unityMallocMutex;

/*-----------------------------------------------------------*/

/**
 * @brief Enter a critical section for unity_malloc.
 */
static void IotTest_EnterCritical( void )
{
    IotMutex_Lock( &_unityMallocMutex );
}

/*-----------------------------------------------------------*/

/**
 * @brief Exit a critical section for unity_malloc.
 */
static void IotTest_ExitCritical( void )
{
    IotMutex_Unlock( &_unityMallocMutex );
}

/*-----------------------------------------------------------*/

/**
 * @brief Parses command line arguments.
 *
 * @param[in] argc Number of arguments passed to main().
 * @param[in] argv Arguments vector passed to main().
 * @param[out] pDisableNetworkTests Set to `true` if `-n` is given, `false` otherwise.
 * @param[out] pDisableLongTests Set to `true` if `-l` is not given, `true` otherwise.
 */
#if IOT_TEST_DEMO != 1
    static void _parseArguments( int argc,
                                 char ** argv,
                                 bool * pDisableNetworkTests,
                                 bool * pDisableLongTests )
    {
        int i = 1;
        const char * pOption = NULL;
        size_t optionLength = 0;

        /* Set default values. */
        *pDisableNetworkTests = false;
        *pDisableLongTests = true;

        for( i = 1; i < argc; i++ )
        {
            /* Get argument string and length. */
            pOption = argv[ i ];
            optionLength = strlen( pOption );

            /* Valid options have the format "-X", so they must be 2 characters long. */
            if( optionLength != 2 )
            {
                continue;
            }

            /* The first character of a valid option must be '-'. */
            if( pOption[ 0 ] != '-' )
            {
                continue;
            }

            switch( pOption[ 1 ] )
            {
                /* Disable tests requiring network if -n is given. */
                case 'n':
                    *pDisableNetworkTests = true;
                    break;

                /* Enable long tests if -l is given. */
                case 'l':
                    *pDisableLongTests = false;
                    break;

                default:
                    break;
            }
        }
    }
#endif /* if IOT_TEST_DEMO == 1 */

/*-----------------------------------------------------------*/

int main( int argc,
          char ** argv )
{
    IOT_FUNCTION_ENTRY( int, EXIT_SUCCESS );
    bool mallocMutexCreated = false;

    /* Create the mutex that guards the Unity malloc overrides. */
    mallocMutexCreated = IotMutex_Create( &_unityMallocMutex, false );

    if( mallocMutexCreated == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( EXIT_FAILURE );
    }

    /* Provide Unity with functions for critical sections. */
    unity_provide_critical_section( IotTest_EnterCritical, IotTest_ExitCritical );

    /* This file is also used to test the demos. When testing demos, the demo main
     * function is called. */
    #if IOT_TEST_DEMO == 1
        status = DemoMain( argc, argv );
    #else
        /* Unity setup. */
        UnityFixture.Verbose = 1;
        UnityFixture.RepeatCount = 1;
        UnityFixture.NameFilter = NULL;
        UnityFixture.GroupFilter = NULL;
        UNITY_BEGIN();
        /* Parse command-line arguments for the tests. */
        bool disableNetworkTests = false, disableLongTests = false;
        _parseArguments( argc, argv, &disableNetworkTests, &disableLongTests );

        /* Call the test runner function. */
        RunTests( disableNetworkTests, disableLongTests );

        /* Return failure if any tests failed. */
        if( UNITY_END() != 0 )
        {
            IOT_SET_AND_GOTO_CLEANUP( EXIT_FAILURE );
        }
    #endif /* if IOT_TEST_DEMO == 1 */

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( mallocMutexCreated == true )
    {
        IotMutex_Destroy( &_unityMallocMutex );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/
