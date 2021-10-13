#ifndef UNITY_RUNNER_H
#define UNITY_RUNNER_H

#include "unity.h"
#include "unity_fixture_internals.h"
#include <string.h>

static int selected( const char * filter,
                     const char * name )
{
    if( filter == 0 )
    {
        return 1;
    }

    return strstr( name, filter ) ? 1 : 0;
}

static int testSelected( const char * test )
{
    return selected( UnityFixture.NameFilter, test );
}

static int groupSelected( const char * group )
{
    return selected( UnityFixture.GroupFilter, group );
}

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
