# Tinycbor library source files.
add_library( tinycbor SHARED
             tinycbor/src/cborencoder.c
             tinycbor/src/cborencoder_close_container_checked.c
             tinycbor/src/cborerrorstrings.c
             tinycbor/src/cborparser.c
             tinycbor/src/cborparser_dup_string.c
             tinycbor/src/cborpretty.c
             tinycbor/src/cborpretty_stdio.c )

# Link math library.
target_link_libraries( tinycbor m )

# Disable all warnings for this third-party library.
target_compile_options( tinycbor
                        PRIVATE
                        $<$<OR:$<C_COMPILER_ID:Clang>,$<C_COMPILER_ID:AppleClang>,$<C_COMPILER_ID:GNU>>:
                        -w> )
