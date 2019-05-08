# Unity test framework.
add_library( unity
             unity/unity.c
             unity/fixture/unity_fixture.c
             unity/fixture/unity_memory_mt.c )

# Unity test framework include paths.
target_include_directories( unity SYSTEM
                            PUBLIC ${PROJECT_SOURCE_DIR}/third_party/unity/unity
                            PUBLIC ${PROJECT_SOURCE_DIR}/third_party/unity/unity/fixture )

# Disable all warnings for this third-party library.
target_compile_options( unity
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w> )
