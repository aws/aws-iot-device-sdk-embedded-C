#include "custom_unity_runner.h"

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

        if( !UnityFixture.Verbose )
        {
            UNITY_OUTPUT_CHAR( '.' );
        }

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
