#!/usr/bin/env python3
import subprocess
import sys
import argparse
import os
import zipfile


def run_cmd(cmd):
    """
    Execute the input command on the shell.
    """
    print(f"Executing command: {cmd}")
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            shell=True,
            encoding="utf-8",
            check=True,
            timeout=180,
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        result = e.stdout
        return result


def get_lib_paths(root):
    """
    Get all of the paths, relative to the root, to the libraries under the
    standard and aws library folders.
    """
    libs_classifications = ["standard", "aws"]
    abs_lib_paths = []

    for lib in libs_classifications:
        libs_path = os.path.join(root, "libraries", lib)
        lib_dirs = os.listdir(libs_path)
        abs_lib_paths += list(map(lambda lib_dir: os.path.join(libs_path, lib_dir), lib_dirs))
    return abs_lib_paths


def main():
    """
    Generate documentation and optionally zip it up.
    """
    parser = argparse.ArgumentParser(description="Generate all doxygen and optionally zip it.")
    parser.add_argument("-r", "--root", action="store", required=True, dest="root", help="CSDK repo root path.")
    parser.add_argument("-z", "--zip", action="store_true", required=False, help="Zip all doxygen output")
    args = parser.parse_args()
    sdk_root = args.root
    doZip = args.zip

    # Get the absolute paths to all of the libraries in the CSDK.
    abs_sdk_root = os.path.abspath(sdk_root)
    abs_lib_paths = get_lib_paths(abs_sdk_root)
    abs_doxy_paths = []

    # Generate the doxygen for all of the libraries.
    for abs_lib_path in abs_lib_paths:
        abs_doxy_path = os.path.join(abs_lib_path, "docs", "doxygen")
        if os.path.exists(abs_doxy_path):
            os.chdir(abs_lib_path)
            run_cmd("doxygen docs/doxygen/config.doxyfile")
            abs_doxy_paths.append(abs_doxy_path)

    # Generate the doxygen for the CSDK last to use the tags from the libraries.
    os.chdir(abs_sdk_root)
    run_cmd("doxygen docs/doxygen/config.doxyfile")
    abs_doxy_paths.append(os.path.join(abs_sdk_root, "docs", "doxygen"))

    # Zip up if desired.
    if doZip:
        print(f"Zipping up to {abs_sdk_root}{os.path.sep}doxygen.zip...")
        doxy_zip = zipfile.ZipFile("doxygen.zip", mode="w")
        try:
            for abs_doxy_path in abs_doxy_paths:
                abs_output_dir = os.path.join(abs_doxy_path, "output")
                for out_root, _, out_files in os.walk(abs_output_dir):
                    rel_out_root = os.path.relpath(out_root, abs_sdk_root)
                    for out_file in out_files:
                        doxy_zip.write(os.path.join(rel_out_root, out_file))
        finally:
            doxy_zip.close()


if __name__ == "__main__":
    main()
