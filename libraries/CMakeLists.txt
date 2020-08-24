# Add all modules.
file(GLOB standard_modules "${MODULES_DIR}/standard/*")
file(GLOB aws_modules "${MODULES_DIR}/aws/*")
foreach(module IN LISTS standard_modules aws_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()

add_subdirectory(${3RDPARTY_DIR})
