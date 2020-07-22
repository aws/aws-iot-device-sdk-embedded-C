function(module)
    cmake_parse_arguments(
        PARSE_ARGV 0
        "ARG"                          # Prefix of parsed results.
        "INTERNAL;INTERFACE;KERNEL"    # Option arguments.
        "NAME"                         # One value arguments.
        ""                             # Multi value arguments.
    )
    message(${ARG_NAME})
    add_library(${ARG_NAME})
endfunction()

# Add source files to a module.
function(module_sources arg_module)
    target_sources(${arg_module} ${ARGN})
endfunction()

# Add include directories to a module.
function(module_include_dirs arg_module)
    target_include_directories(${arg_module} ${ARGN})
endfunction()

function(set_lib_metadata arg_metadata_name arg_metadata_val)
endfunction()
