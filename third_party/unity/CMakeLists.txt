# Unity test framework.
add_library( unity SHARED
             unity/src/unity.c
             unity/extras/fixture/src/unity_fixture.c
             unity_memory_mt.c )
