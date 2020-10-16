This demonstration downloads files from URLs received via AWS IoT Jobs.
Details are available in the usage function at the top of jobs_demo.c.

This demo is intended for Linux platforms with the GCC toolchain,
curl, and libmosquitto installed.  To build this demo, run make.

To install curl and libmosquitto on a Debian or Ubuntu host, run:

    apt install curl libmosquitto-dev

To build the latest version of libmosquitto with ALPN support,
clone the repository at https://github.com/eclipse/mosquitto ,
and follow the instructions in compiling.txt within the repo.
