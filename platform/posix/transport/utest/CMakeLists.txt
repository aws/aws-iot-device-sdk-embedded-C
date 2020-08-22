include("../transportFilePaths.cmake")
project ("transport unit test")
cmake_minimum_required (VERSION 3.13)

# CMock does not have a built-in C parser. 
# https://github.com/ThrowTheSwitch/CMock/issues/71
# Therefore, header files need to be preprocessed before mocks are generated.

# ====================  Define your project name (edit) ========================
set(project_name "transport")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
                ${OPENSSL_INCLUDE_DIR}/arpa/inet.h
                ${OPENSSL_INCLUDE_DIR}/x86_64-linux-gnu/sys/socket.h
                ${OPENSSL_INCLUDE_DIR}/netdb.h
                ${CMAKE_CURRENT_LIST_DIR}/mocks/close.h
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
            ${SOCKETS_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
            ${OPENSSL_INCLUDE_DIR}/arpa
            ${OPENSSL_INCLUDE_DIR}/x86_64-linux-gnu/sys
            ${OPENSSL_INCLUDE_DIR}
            mocks
        )

# =============================  (end edit)  ===================================

set(mock_name "sockets_mock")
set(real_name "sockets_real")

create_mock_list(${mock_name}
                "${mock_list}"
                "${ROOT_DIR}/tools/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

list(APPEND utest_link_list
            lib${real_name}.a
            -l${mock_name}
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "sockets_utest")
set(utest_source "sockets_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

target_compile_definitions(${utest_name} PUBLIC
            ${mock_define_list}
        )

        target_compile_definitions(${real_name} PUBLIC
            ${mock_define_list}
        )