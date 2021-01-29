include(CheckSymbolExists)

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
    set(DEFINED_MACROS "")
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
                    list(APPEND DEFINED_MACROS "${optional_macro_definition}")
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
                    list(APPEND CMAKE_REQUIRED_DEFINITIONS -D${required_macro_definition})
                    list(APPEND DEFINED_MACROS "${required_macro_definition}")
                    continue()
                endif()
                # Check if MACRO_DEFINITIONS_FILES_TO_CHECK has the required macros defined already.
                get_target_property(APPLICATION_INCLUDES ${application_target} INCLUDE_DIRECTORIES)
                set(CMAKE_REQUIRED_INCLUDES ${APPLICATION_INCLUDES})
                unset(HAVE_${required_macro_definition} CACHE)
                check_symbol_exists(${required_macro_definition} ${MACRO_DEFINITIONS_FILES_TO_CHECK} HAVE_${required_macro_definition})
                # Append to the right list depending on whether definition was found.
                if(HAVE_${required_macro_definition})
                    list(APPEND DEFINED_MACROS "${required_macro_definition}")
                else()
                    list(APPEND MISSING_REQUIRED_MACROS "${required_macro_definition}")
                endif()
            endforeach()
        endif()
        # Print the error when certain required macros are not defined.
        if(DEFINED_MACROS)
            string(REPLACE ";" ", " DEFINED_MACROS "${DEFINED_MACROS}")
            message("Found the following definitions for ${application_target}: ${DEFINED_MACROS}")
        endif()
        if(MISSING_REQUIRED_MACROS)
            string(REPLACE ";" ", " MISSING_REQUIRED_MACROS "${MISSING_REQUIRED_MACROS}")
            message("Cannot build ${application_target} because the following required definitions are missing: ${MISSING_REQUIRED_MACROS}")
            message("To run ${application_target}, define required macros in ${application_target}/demo_config.h.")
            set_target_properties(${application_target} PROPERTIES EXCLUDE_FROM_ALL true)
        else()
            message("All required definitions for ${application_target} were found - Adding to default target.")
        endif()
    endforeach()
endfunction()
