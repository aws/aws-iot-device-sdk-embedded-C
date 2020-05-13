include("../filePaths.cmake")
project ("http unit test")
cmake_minimum_required (VERSION 3.13)

# ====================  Define your project name (edit) ========================
set(project_name "http")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
            ""
        )
# list the directories your mocks need
list(APPEND mock_include_list
            ""
        )
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
            ""
       )

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${HTTP_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${HTTP_INCLUDE_PUBLIC_DIRS}
            ${HTTP_INCLUDE_PRIVATE_DIRS}
            "${ROOT_DIR}/platform/include"
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${HTTP_INCLUDE_PUBLIC_DIRS}
            ${HTTP_INCLUDE_PRIVATE_DIRS}
            ${HTTP_TEST_INCLUDE_PRIVATE_DIRS}
            "${ROOT_DIR}/platform/include"
        )

# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    ""
        )

list(APPEND utest_link_list
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "${project_name}_utest")
set(utest_source "${project_name}_utest.c")
set (logging_source ${MODULES_DIR})
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
