# Demo programs

This directory contains source files for demo executables. Its subdirectories are organized as follows:
- `app` <br>
  Source files for demo runner executables (i.e. the `main()` function).
- `include` <br>
  Common headers for the demo executables. These headers handle argument parsing and logging which are common to all demos.
- `source` <br>
  Platform-independent demo sources. The files in this directory contain the majority of the demo code. The demo runner in `app` calls demo functions implemented in this directory.

The configuration file for the demos, `iot_config.h`, is in this directory. This file is intended to hold all configuration for the demos and libraries. See [Global configuration](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/global_config.html) for settings that affect all demos and libraries; see each library's documentation for library-specific settings.

For information on building and running the demos, see [Building the SDK](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/building.html).
