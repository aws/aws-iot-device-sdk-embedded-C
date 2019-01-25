# Unity test framework.
add_library( unity SHARED
             unity.c
             fixture/unity_fixture.c
             fixture/unity_memory_mt.c )
