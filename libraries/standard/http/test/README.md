# Instructions for running the tests:

1. In your GNU compatible environment like WSL, mingw, Linux OS, MAC OS, etc., open a terminal.
1. To get all the required installation scripts, clone this repo: https://github.com/dan4thewin/mock4thewin.
1. Go to the repo directory: `cd \{mock4thewin repo}`
1. Run this command to install: `sudo ./install /usr/local`
1. To get another required tool, clone this repo https://github.com/dan4thewin/ctags-xref and follow the instructions in the root README.md.
1. Go back to the HTTP Client test folder: `cd {CSDK_ROOT}/libraries/standard/http/test`
1. Run this command to build and run the tests: `make test`
1. This framework automatically generates test-\[function_name\] function_name.c files for ease in mocking. Also auto-generated are *gcov* related files for coverage information.

# Writing Unit Tests
1. Make a file under {CSDK_ROOT}/libraries/standard/http/test named "test-\[function_name\].c"  
   For example {CSDK_ROOT}/libraries/standard/http/test/test-HTTPClient_AddHeader.c
1. See https://gist.github.com/dan4thewin/6f708bf635f6cb647d9f7bc7f55e4706#the-complete-unit-test for an example unit tests and how to test assert.
1. Any mocked external functions should go into "common.h".
1. Build, run, and get coverage with: `make test`
