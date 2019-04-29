# Unity test framework.
add_library( unity
             unity/unity.c
             unity/fixture/unity_fixture.c
             unity/fixture/unity_memory_mt.c )

# Disable all warnings for this third-party library.
target_compile_options( unity
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w> )
