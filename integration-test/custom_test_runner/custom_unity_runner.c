#include "custom_unity_runner.h"

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
                            unsigned int line )
{
    if( testSelected( name ) && groupSelected( group ) )
    {
        Unity.TestFile = file;
        Unity.CurrentTestName = printableName;
        Unity.CurrentTestLineNumber = line;

        Unity.NumberOfTests++;

        UnityMalloc_StartTest();
        UnityPointer_Init();

        UNITY_EXEC_TIME_START();

        if( TEST_PROTECT() )
        {
            setup();
            testBody();
        }

        if( TEST_PROTECT() )
        {
            teardown();
        }

        if( TEST_PROTECT() )
        {
            UnityPointer_UndoAllSets();

            if( !Unity.CurrentTestFailed )
            {
                UnityMalloc_EndTest();
            }
        }

        UNITY_EXEC_TIME_STOP();
        UnityConcludeTest();
    }
}
