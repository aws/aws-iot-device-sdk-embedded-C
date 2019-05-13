# Platform layer

**Main documentation page:** [Platform layer](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/platform/index.html)

This directory contains the headers and sources of the platform layer. Its subdirectories are organized as follows:
- `include` <br>
  Platform layer headers. Headers used across multiple ports are placed in this directory.
  - `atomic` <br>
    Implementations of atomic operations.
  - `posix`, `win32`, `...` <br>
    Headers specific to a port.
- `source` <br>
  Platform layer sources.
  - `network`
    Source files of network implementations that are not specific to a specific port.
  - `posix`, `win32`, `...` <br>
    Source files of a specific port.

When porting this SDK to a new platform, only files in this directory should be modified. See [Porting guide](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/guide_developer_porting.html) for instructions.
