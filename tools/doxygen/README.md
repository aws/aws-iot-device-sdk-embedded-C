# Generate all Doxygen

## Prerequisites

- [Git](https://git-scm.com/downloads/)
- [Python 3+](https://www.python.org/downloads/)

## Output

This script generates all of the Doxygen documentation for the CSDK and its
library spoke repos.
Any Doxygen warnings from generation will print out to the console.
Optionally, one can also choose to zip up the generated Doxygen documentation.

## Usage

### Preliminary

Ensure that all of the library spoke repositories are cloned before running this script.

```console
cd aws-iot-device-sdk-embedded-C
git submodule update --init --checkout libraries/standard libraries/aws
```

### Generate Doxygen

You can run this script from anywhere with the path to the CSDK repo root.

```console
python3 generate_docs.py --root <CSDK_REPO_ROOT>
```

If the `--root` option is not given, then the script assumes the current working
directory is the CSDK repo root.

```console
python3 tools/doxygen/generate_docs.py
```

### Generate Doxygen Zipfile

Pass the `--zip` or `-z` option to create a zip file named "**doxygen.zip**" in the
current working directory.

```console
python3 tools/doxygen/generate_docs.py --zip
```
