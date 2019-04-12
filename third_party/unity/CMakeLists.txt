# Unity test framework.
add_library( unity SHARED
             unity/unity.c
             unity/fixture/unity_fixture.c
             unity/fixture/unity_memory_mt.c )
