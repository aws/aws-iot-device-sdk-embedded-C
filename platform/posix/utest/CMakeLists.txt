project ("posix unit test")
cmake_minimum_required (VERSION 3.2.0)

# ====================  Define your project name (edit) ========================
set(project_name "posix")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
            ${CMAKE_CURRENT_LIST_DIR}/mocks/time_api.h
        )
# list the directories your mocks need
list(APPEND mock_include_list
            ${PLATFORM_DIR}/include
        )
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
            ""
        )

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${PLATFORM_DIR}/posix/retry_utils_posix.c
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            ${PLATFORM_DIR}/include
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            ${PLATFORM_DIR}/include
            /usr/include
            mocks
        )

# =============================  (end edit)  ===================================

# Create the target for unit testing the clock
set(real_name "clock_real")
set(mock_name "clock_mock")

create_mock_list(${mock_name}
                "${mock_list}"
                "${ROOT_DIR}/tools/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

set(real_source_files
        ${PLATFORM_DIR}/posix/clock_posix.c
   )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
)

set(utest_link_list
        lib${real_name}.a
        -l${mock_name}
   )

set(utest_dep_list
        ${real_name}
   )

set(utest_name "clock_utest")
set(utest_source "clock_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
