# Test programs

This directory contains source files for the test executables. The test executable source (i.e. the `main()` function) is `iot_tests.c` and the configuration header used when building the tests is `iot_config.h`. The configuration header is intended to hold all configuration for the tests and libraries. See [Global configuration](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/global_config.html) for settings that affect all tests and libraries; see each library's documentation for library-specific settings.

The test code sources are placed with their libraries and not in this directory. For example, the sources for the MQTT tests are in `libraries/standard/mqtt/test`.

For information on building and running the tests, see [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/building.html).
