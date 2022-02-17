project ("http system test")
cmake_minimum_required (VERSION 3.2.0)

# Include HTTP library's source and header path variables.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/coreHTTP/httpFilePaths.cmake )

# Include backoffAlgorithm library file path configuration.
include( ${CMAKE_SOURCE_DIR}/libraries/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set(project_name "http_system")

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${HTTP_SOURCES}
            ${BACKOFF_ALGORITHM_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${HTTP_INCLUDE_PUBLIC_DIRS}
            ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${HTTP_INCLUDE_PUBLIC_DIRS}
            ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
        )

# =====================  Create Library Target (end edit)  =====================

set(real_name "${project_name}_real")

#[[the following three functions exist in the "create_real_library" method of the cmock
create_test tool, but are localized here to allow for the removal of the "-Wpedantic" flag,
which raises build errors in http_parser due to differing language standards]]
add_library(${real_name} STATIC
        ${real_source_files}
    )
target_include_directories(${real_name} PUBLIC
        ${real_include_directories}
    )
set_target_properties(${real_name} PROPERTIES
            COMPILE_FLAGS "-Wextra \
                -fprofile-arcs -ftest-coverage -fprofile-generate \
                -Wno-unused-but-set-variable \
                -Wno-unused-parameter"
            LINK_FLAGS "-fprofile-arcs -ftest-coverage \
                -fprofile-generate "
            ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib
        )

# =============  Create Test Target & Assign Build-Configured Defines  ==========

list(APPEND stest_link_list
            lib${real_name}.a
        )

list(APPEND stest_dep_list
            ${real_name}
            clock_posix
            openssl_posix
        )

set(stest_name "${project_name}_test")
set(stest_source "${project_name}_test.c")
create_test(${stest_name}
            ${stest_source}
            "${stest_link_list}"
            "${stest_dep_list}"
            "${test_include_directories}"
        )

set_macro_definitions(TARGETS ${stest_name}
                      REQUIRED
                        "ROOT_CA_CERT_PATH"
                        "SERVER_HOST"
                        "HTTPS_PORT"
                      FILES_TO_CHECK
                        "test_config.h")
