# Test programs

This directory contains source files for test executables. Its subdirectories are organized as follows:
- `common`, `defender`, `...` <br>
  Platform-independent test sources for individual libraries.

The test executable source (i.e. the `main()` function) is `iot_tests.c`.

The configuration file for the tests, `iot_config.h`, is in this directory. This file is intended to hold all configuration for the tests and libraries. See [Global configuration](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/global_config.html) for settings that affect all tests and libraries; see each library's documentation for library-specific settings.

For information on building and running the tests, see [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/building.html).
