# Test programs

This directory contains source files for test executables. Its subdirectories are organized as follows:
- `app` <br>
  Source files for test runner executables (i.e. the `main()` function). These are platform-dependent files named after the platform they support (e.g. `iot_tests_posix.c`, `iot_tests_win32.c`, etc.).
- `common`, `defender`, `...` <br>
  Platform-independent test sources for individual libraries.

The configuration file for the tests, `iot_config.h`, is in this directory. This file is intended to hold all configuration for the tests and libraries. See [Global configuration](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/global_config.html) for settings that affect all tests and libraries; see each library's documentation for library-specific settings.

For information on building and running the tests, see [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/building.html).
