# Unity test framework.
add_library( unity SHARED
             unity.c
             fixture/unity_fixture.c
             fixture/unity_memory_mt.c )

set_target_properties( unity PROPERTIES PUBLIC_HEADER
                       "unity.h;fixture/unity_fixture.h;fixture/unity_fixture_malloc_overrides.h" )

set_target_properties( unity PROPERTIES PRIVATE_HEADER
                       "unity_internals.h;fixture/unity_fixture_internals.h" )
