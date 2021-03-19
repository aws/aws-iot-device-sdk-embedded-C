include(CheckSymbolExists)

# This function can be called to define a set of required and optional macros for a build target.
#
# If a CMake variable is defined with the same name as a required macro, it will be
# passed to the target. Otherwise, `FILES_TO_CHECK` (default: demo_config.h)
# will be checked to see if it already has the macro defined. An optional macro will
# only perform the first step.
function(set_macro_definitions)
    set(multiValueArgs TARGETS REQUIRED OPTIONAL FILES_TO_CHECK)
    cmake_parse_arguments(MACRO_DEFINITIONS "" "" "${multiValueArgs}" ${ARGN})
    # Check for missing parameters.
    if(NOT DEFINED MACRO_DEFINITIONS_TARGETS)
        message("At least one target is required when setting macro definitions through CMake.")
        return()
    endif()
    # Default file to check is demo_config.h
    if(NOT DEFINED MACRO_DEFINITIONS_FILES_TO_CHECK)
        set(MACRO_DEFINITIONS_FILES_TO_CHECK "demo_config.h")
    endif()
    set(CMAKE_REQUIRED_DEFINITIONS "")
    set(DEFINED_MACROS_FROM_CMAKE "")
    set(DEFINED_MACROS_FROM_FILE "")
    set(MISSING_REQUIRED_MACROS "")
    foreach(application_target ${MACRO_DEFINITIONS_TARGETS})
        if(DEFINED MACRO_DEFINITIONS_OPTIONAL)
            foreach(optional_macro_definition ${MACRO_DEFINITIONS_OPTIONAL})
                if(DEFINED ${optional_macro_definition})
                    # Compile the application with the macro definition if it is defined.
                    target_compile_definitions(
                        ${application_target} PRIVATE
                            ${optional_macro_definition}="${${optional_macro_definition}}"
                    )
                    list(APPEND DEFINED_MACROS_FROM_CMAKE "${optional_macro_definition}")
                endif()
            endforeach()
        endif()
        if(DEFINED MACRO_DEFINITIONS_REQUIRED)
            foreach(required_macro_definition ${MACRO_DEFINITIONS_REQUIRED})
                # Check if definition was passed as CMake flag.
                if(DEFINED ${required_macro_definition})
                    target_compile_definitions(
                        ${application_target} PRIVATE
                            ${required_macro_definition}="${${required_macro_definition}}"
                    )
                    # This variable adds definitions to the file being run against `check_symbol_exists`.
                    list(APPEND CMAKE_REQUIRED_DEFINITIONS -D${required_macro_definition})
                    list(APPEND DEFINED_MACROS_FROM_CMAKE "${required_macro_definition}")
                    continue()
                endif()
                # Check if MACRO_DEFINITIONS_FILES_TO_CHECK has the required macros defined already.
                get_target_property(APPLICATION_INCLUDES ${application_target} INCLUDE_DIRECTORIES)
                set(CMAKE_REQUIRED_INCLUDES ${APPLICATION_INCLUDES})
                set(CMAKE_REQUIRED_QUIET TRUE)
                unset(HAVE_${required_macro_definition} CACHE)
                check_symbol_exists(${required_macro_definition} ${MACRO_DEFINITIONS_FILES_TO_CHECK} HAVE_${required_macro_definition})
                # Append to the right list depending on whether definition was found.
                if(HAVE_${required_macro_definition})
                    list(APPEND DEFINED_MACROS_FROM_FILE "${required_macro_definition}")
                else()
                    list(APPEND MISSING_REQUIRED_MACROS "${required_macro_definition}")
                endif()
            endforeach()
        endif()
        # Log the file of the defined macros
        list(LENGTH DEFINED_MACROS_FROM_FILE DEFINED_MACROS_FROM_FILE_LENGTH)
        if(DEFINED_MACROS_FROM_FILE_LENGTH GREATER 0)
            message("Using values in ${MACRO_DEFINITIONS_FILES_TO_CHECK} to define the following macros for ${application_target}:")
            foreach(defined_macro_from_file ${DEFINED_MACROS_FROM_FILE})
                message("${defined_macro_from_file}")
            endforeach()
        endif()
        # Log the value of the macros passed through CMake
        list(LENGTH DEFINED_MACROS_FROM_CMAKE DEFINED_MACROS_FROM_CMAKE_LENGTH)
        if(DEFINED_MACROS_FROM_CMAKE_LENGTH GREATER 0)
            message("Using the passed CMake arguments to define the following macros for ${application_target}:")
            foreach(defined_macro_from_cmake ${DEFINED_MACROS_FROM_CMAKE})
                message("${defined_macro_from_cmake} = ${${defined_macro_from_cmake}}")
            endforeach()
        endif()
        set(DEFINED_MACROS ${DEFINED_MACROS_FROM_CMAKE} ${DEFINED_MACROS_FROM_FILE})
        # Print the error when certain required macros are not defined.
        if(DEFINED_MACROS)
            string(REPLACE ";" ", " DEFINED_MACROS "${DEFINED_MACROS}")
            message("Found the following definitions for ${application_target}: ${DEFINED_MACROS}")
        endif()
        if(MISSING_REQUIRED_MACROS)
            string(REPLACE ";" ", " MISSING_REQUIRED_MACROS "${MISSING_REQUIRED_MACROS}")
            message("WARNING: ${application_target} missing definitions for macros: ${MISSING_REQUIRED_MACROS}")
            message("To run ${application_target}, define required macros in ${application_target}/demo_config.h.\n")
            set_target_properties(${application_target} PROPERTIES EXCLUDE_FROM_ALL true)
        else()
            message("All required definitions for ${application_target} were found - Adding to default target.\n")
        endif()
    endforeach()
endfunction()

# This macro makes the value of some CMake variable have the same value as its aliases.
macro(set_alias var_name)
    set(multiValueArgs ALIASES)
    cmake_parse_arguments(CMAKE_VAR "" "" "${multiValueArgs}" ${ARGN})
    # Check for missing parameters.
    if(NOT DEFINED CMAKE_VAR_ALIASES)
        message("At least one alias is required when setting alias for CMake configuration.")
        return()
    endif()
    foreach(alias_name ${CMAKE_VAR_ALIASES})
        if(DEFINED ${var_name})
            set(${alias_name} "${${var_name}}")
        elseif(DEFINED ${alias_name})
            set(${var_name} "${${alias_name}}")
        endif()
    endforeach()
endmacro()
