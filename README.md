# AWS IoT Device SDK C v4.0.0

## Development branch
This branch currently hosts development of the next iteration of the AWS IoT Embedded C SDK version 4. It is currently a work in progress and should not be used to create any products.  We will update this README when that status changes.

## Building and Running Demos

This SDK builds with [CMake](https://cmake.org/), a cross-platform build tool.

### Prerequisites
- CMake 3.5.0 or later and a C90 compiler.
- A supported operating system. The ports provided with this repo are expected to work with all recent versions of the following operating systems, although we cannot guarantee the behavior on all systems.
    - On Linux systems, installation of OpenSSL development libraries and header files, *version 1.0.2g or later*, are required. The OpenSSL development libraries are usually called something like `libssl-dev` or `openssl-devel` when installed through a package manager.

### Build Steps
1. Go to the root directory of this repository.
1. Create build directory: `mkdir build && cd build`
1. Run *cmake* while inside build directory: `cmake ..`
1. Run this command to build the demos: `make`
1. Go to the `build/bin` directory and run any demo executables from there.
1. To run demos prefixed with `http_`:
    1. Install `Python 3` if it is not yet installed in your system: `sudo apt-get install python3`
    1. Run the following from the root directory of this repository: `python3 tools/http-echo-server/http_server.py &`
