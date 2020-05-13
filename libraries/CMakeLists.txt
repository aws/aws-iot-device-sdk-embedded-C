include("${ROOT_DIR}/tools/cmock/create_test.cmake")

# Add all CMakeLists.txt in 3rdparty and standard folders.
file(GLOB standard_modules "${MODULES_DIR}/standard/*")
file(GLOB 3rdparty_modules "${3RDPARTY_DIR}/*")
foreach(module IN LISTS standard_modules 3rdparty_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()
