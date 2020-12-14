project( "ota_pal unit test" )
cmake_minimum_required( VERSION 3.2.0 )

#== ==================  Define your project name (edit) ========================
set( project_name "ota_pal" )

#== ===================  Create your mock here  (edit)  ========================

#list the files to mock here
list( APPEND mock_list
      ${CMAKE_CURRENT_LIST_DIR}/mocks/stdio_api.h
      ${CMAKE_CURRENT_LIST_DIR}/mocks/openssl_api.h
      ${CMAKE_CURRENT_LIST_DIR}/mocks/unistd_api.h
      )
#list the directories your mocks need
list( APPEND mock_include_list
      ${LOGGING_INCLUDE_DIRS}
      ${PLATFORM_DIR}/include
      )
#list the definitions of your mocks to control what to be included
list( APPEND mock_define_list
      ""
      )

#== =============== Create the library under test here (edit) ==================

#list the files you would like to test here
list( APPEND real_source_files
      "${PLATFORM_DIR}/posix/ota_pal/source/ota_pal_posix.c"
      )

#list the directories the module under test includes
list( APPEND real_include_directories
      "${MODULES_DIR}/aws/ota-for-aws-iot-embedded-sdk/source/include"
      "${PLATFORM_DIR}/posix/ota_pal/source/include"
      ${OPENSSL_INCLUDE_DIR}
      ${CMAKE_CURRENT_LIST_DIR}
      ${CMAKE_CURRENT_LIST_DIR}/mocks
      )

#== ===================  Create UnitTest Code here (edit)  =====================

#list the directories your test needs to include
list ( APPEND test_include_directories
       ${CMAKE_CURRENT_BINARY_DIR}/include
       ${CMAKE_CURRENT_LIST_DIR}
       ${MODULES_DIR}/aws/ota-for-aws-iot-embedded-sdk/source/include
       /usr/include/x86_64-linux-gnu/sys
       mocks
       )

#== ===========================  (end edit)  ===================================
set ( mock_name "ota_pal_mocks" )
set ( real_name "ota_pal_real" )

create_mock_list(${mock_name}
                "${mock_list}"
                "${ROOT_DIR}/tools/cmock/ota.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library ( ${real_name}
                      "${real_source_files}"
                      "${real_include_directories}"
                      "${mock_name}"
                      )

list(APPEND utest_link_list
      lib${real_name}.a
      )

list ( APPEND utest_dep_list
       ${real_name}
      )

set ( utest_name "ota_pal_posix_utest" )
set ( utest_source "ota_pal_posix_utest.c" )
create_test ( ${utest_name}
              ${utest_source}
              "${utest_link_list}"
              "${utest_dep_list}"
              "${test_include_directories}"
              )
