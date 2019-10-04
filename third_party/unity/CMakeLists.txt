# Unity test framework source files.
set( UNITY_SOURCES
     unity/unity.c
     unity/fixture/unity_fixture.c
     unity/fixture/unity_memory_mt.c )

# Unity test framework headers (for folder organization only).
set( UNITY_HEADERS
     unity/unity.h
     unity/unity_internals.h
     unity/fixture/unity_fixture.h
     unity/fixture/unity_fixture_internals.h
     unity/fixture/unity_fixture_malloc_overrides.h )

# Unity test framework target.
add_library( unity
             ${UNITY_SOURCES} ${UNITY_HEADERS} )

# Unity test framework include paths.
target_include_directories( unity SYSTEM
                            PUBLIC unity
                            PUBLIC unity/fixture )

# Disable all warnings for this third-party library.
target_compile_options( unity
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w>
                        $<$<C_COMPILER_ID:MSVC>:
                        /W0 /D_CRT_SECURE_NO_WARNINGS> )

# Organization of Unity in folders.
set_property( TARGET unity PROPERTY FOLDER third_party )
source_group( include FILES ${UNITY_HEADERS} )
source_group( source FILES ${UNITY_SOURCES} )
