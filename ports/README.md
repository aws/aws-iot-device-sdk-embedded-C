# Platform ports

This directory contains the desktop OS ports. Each port implements the functions of the platform layer interface for a specific desktop OS. See [Platform layer](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/platform/index.html) for details on the platform layer interface.

Its subdirectories are organized as follows:
- `common` <br>
  Port files that are not specific to a single port. These headers are used across all of the desktop OS ports.
  - `include` <br>
    Port headers that are not specific to a single port, such as the atomic and network headers.
    - `atomic` <br>
      Implementations of atomic operations.
  - `src` <br>
    Port sources that are not specific to a single port, such as the network implementations.
- `template` <br>
  Empty port sources containing stubbed-out functions. The files in this directory may be used as a starting point for a new port.
- `posix`, `macos`, `win32` <br>
  Port sources and headers for a single implementation. They directory is named after the target OS.

See [Porting guide](https://docs.aws.amazon.com/freertos/latest/lib-ref/c-sdk/main/guide_developer_porting.html) for instructions on how to create a new port.
