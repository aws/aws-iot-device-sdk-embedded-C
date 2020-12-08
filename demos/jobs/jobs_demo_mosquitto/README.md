This demonstration downloads files from URLs received via AWS IoT Jobs.
Details are available in the usage function at the top of jobs_demo.c.

This demo is intended for Linux platforms with the GCC toolchain,
curl, and libmosquitto installed.  To build this demo, run make.

To install curl and libmosquitto on a Debian or Ubuntu host, run:

    apt install curl libmosquitto-dev

Version 1.4.10 of libmosquitto is required to run this demo.
To build the latest version of libmosquitto (1.6.12) for ALPN support,
go to the libmosquitto directory,
and follow the instructions in compiling.txt within the submodule.
