#ifndef UNITY_RUNNER_H
#define UNITY_RUNNER_H

#include "unity.h"
#include "unity_memory.h"
#include "unity_fixture_internals.h"
#include <string.h>

/**
 * @brief A custom runner that makes the standard output of
 * multiple test groups match the standard output of the default
 * runner for a single test group.
 */
void CustomUnityTestRunner( unityfunction * setup,
                            unityfunction * testBody,
                            unityfunction * teardown,
                            const char * printableName,
                            const char * group,
                            const char * name,
                            const char * file,
                            unsigned int line );

/* Undefine this macro defined by unity_fixture.h so that a custom
 * runner can be used */
#ifdef TEST
    #undef TEST

/* Define a custom macro that will be used for our tests. */
    #define TEST( group, name )                                  \
    void TEST_ ## group ## _ ## name ## _( void );               \
    void TEST_ ## group ## _ ## name ## _run( void );            \
    void TEST_ ## group ## _ ## name ## _run( void )             \
    {                                                            \
        CustomUnityTestRunner( TEST_ ## group ## _SETUP,         \
                               TEST_ ## group ## _ ## name ## _, \
                               TEST_ ## group ## _TEAR_DOWN,     \
                               "TEST(" # group ", " # name ")",  \
                               TEST_GROUP_ ## group, # name,     \
                               __FILE__, __LINE__ );             \
    }                                                            \
    void TEST_ ## group ## _ ## name ## _( void )
#endif /* ifdef TEST */

#endif /* ifndef UNITY_RUNNER_H */
