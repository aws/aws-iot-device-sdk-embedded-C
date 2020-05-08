# Running Unit Tests

1. In your GNU compatible environment, open a terminal.
1. Install ruby: `sudo apt install ruby-full`
1. Install lcov: `sudo apt install lcov`
1. Go to the root directory of this repository.
1. Update submodules (if you haven't already): `git submodule update --init --recursive` 
1. Create build directory: `mkdir build && cd build`
1. Run cmake while inside build directory: `cmake ..`
1. Run this command to build and run the tests: `make coverage`
1. Go to `build` and open `*_utest_out.txt` to view logs
1. Go to `build/coverage` and open `index.html` to view test coverage results.

# Writing Unit Tests

### Introduction to CMock
**CMock** is a mocking framework, that automatically generates mocks.
It gives the ability to set expectations and implement stubs/callbacks.
This will allow you to call the functions to be tested and the **CMock** generated code will do all the rest for you.

For example suppose your module accesses the internet using sockets, but you want to just test your module (unit) without testing/calling any socket API function as this could be unpredictable, slow, hard to simulate all possible
error scenarios and return codes.
In order to achieve that you tell **CMock** to mock the header file where the socket's APIs reside. For simplicity we will assume the only function used is *func*, **CMock** will generate the following mocks for you:

```
func_Ignore[AndReturn]([return_val]);
func_ExpectAnyArgs[AndReturn]([return_val]);
func_Expect[AndReturn](param1, param2,..., paramN ,[return_val])
func_StubWithCallback(function_callback)
func_ExpectWithArray[AndReturn](param1, [depth1], param2, [depth2], ..., paramN, [depthN], [return_val])
func_ReturnThruPtr_[parameter name](ret_pointer)
func_ReturnArrayThruPtr_parameeter(parameter, len)
func_ReturnMemThruPtr_[parameter name](size, ret_memory)
func_IgnoreArg_[parameter name]()
```
For a detailed explanation about these mocks check the official documentation:
[The **CMock** official website](http://www.throwtheswitch.org/cmock)
[The **CMock** github repository](https://github.com/ThrowTheSwitch/CMock)

### Setting up a new Unit Testing module in C SDK
To setup a module for Unit Testing, as an example we will follow a walkthrough approach for **mqtt** which is located in `libraries/standard/mqtt`.

1. In the directory of the module to be tested, add the following to its CMakeLists.txt:
```cmake
if(BUILD_TESTS)
    add_subdirectory(utest)
endif()
```

1. Create a new directory called `utest`

1. For simplicity, copy the CMakeLists.txt file from `libraries/standard/mqtt` into the new Unit-Test Directory `utest`

1. Create a test source file that ends with  `_utest.c`, it is where your test code will live. You will end up with 2 files in the utest directory (project_name_utest.c and CMakeLists.txt)

1. Edit the copied file (CMakeLists.txt) in the following way
    1. Modify the `project_name` at the top to match the new one to be tested
    1. Replace all headers in `mock_list` with the ones you the source file
       under test uses.
       ```cmake
        list(APPEND mock_list
                    my_file.h
                )
       ```
    1. Replace all the include directories in `mock_include_list` with the
       directories your mocks are using
       ```cmake
        list(APPEND mock_include_list
                    /my/file/dir/needs
                )
        ```
    1. Replace the definitions in `mock_define_list` list with the definitions you see fit for your source files
       ```cmake
       list(APPEND mock_define_list
                    -DMY_DEFINE=1
                )
       ```
       This will create header files in the following form:
       my_file_mock.h which you will have to include from
       your test code (project_name_utest.c)
       This compilation step would create a shared object with the name `project_name_mock.so`

    1. Replace all the files in `real_source_files` with the source files you will
       be testing. This will create a library with the name `project_file_real.a`
       ```cmake
       list(APPEND real_source_files
                    code_to_test.c
                )
       ```
    1. Replace all the dirctories in `real_include_directories`  with the
       directories the source under test will include headers from
       ```cmake
       list(APPEND real_include_directories
                   /my/under/test/source/needs
               )
       ```
       This compilation step would create an object library called `project_name_real.a`
    1. Replace all directories in `test_include_directories` with what the test
       code needs (project_name_utest.c)
       ```cmake
       list(APPEND test_include_directories
                    /my/test/code/needs
                )
        ```

    1. And that's it for this file

    1. At the end, this makefile will create the mock files and 3 object files
       `project_name_mock.so`, `project_name_real.a` and `project_name_utest`

    1. If you'd like to automatically compile your unit tests upon `make coverage`, edit `CMakeLists.txt` in the root directory of this repo to include `project_name_utest`:
        ```cmake
        add_custom_target(coverage
                COMMAND ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
                DEPENDS cmock unity http_utest mqtt_utest project_name_utest
                WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                )
            ```

1. Write your Unit Test code `project_name_utest.c` it is easier if you copy a
   file from another place `mqtt` for example to reuse its skeleton
    A few points to keep in mind:
    * There is no need to write a main function, it is automatically generated
    * Testing functions must start with `test_`
    * We use unity to test and assert results
1.  You should be ready to go by now
    Always remember! If it is not tested, it doesn't work :( ... Happy Testing!
