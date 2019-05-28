# Platform layer

**Main documentation page:** [Platform layer](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/platform/index.html)

This directory contains the headers and sources of the platform layer, implemented for various ports. Its subdirectories are organized as follows:
- `include` <br>
  Platform layer headers that are not specific to a specific port, such as the atomic and network headers.
  - `atomic` <br>
    Implementations of atomic operations.
- `network` <br>
  Implementations of the platform network layer that are not specific to a port.
- `ports` <br>
    Source files of a specific port.
  - `posix`, `win32`, `...` <br>
    Port sources are in a directory named after their target.
  - `template` <br>
    Empty port sources containing stubbed-out functions.

When porting this SDK to a new platform, only files in this directory should be modified. See [Porting guide](https://docs.aws.amazon.com/freertos/latest/lib-ref/html3/main/guide_developer_porting.html) for instructions.
