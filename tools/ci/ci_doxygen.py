#!/usr/bin/env python3

import os
import subprocess
import sys
import filecmp
import junitparser as junit
import re

# CSDK Doxygen Templates path
DOXYGEN_TEMPLATES_PATH = "docs/doxygen_templates"
DOXYGEN_STYLE_FILES = ["style.css", "layout.xml"]
DOXYGEN_CONFIG_FILE = "config.doxyfile"
DOXYGEN_ALLOWED_CUSTOM_CONFIGS = [
    "ALIASES",
    "FIXME",
    "IMAGE_PATH",
    "PREDEFINED",
    "INCLUDE_PATH",
    "EXPAND_AS_DEFINED",
    "EXCLUDE_SYMBOLS",
]
TRANSPORT_INTERFACE_PATH = "platform/include/transport_interface.h"


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


def to_junit(results, platform=""):
    """
    Convert result to junit format.
    """
    report = junit.JUnitXml()
    if not results:
        return report

    platform += platform and "."

    for target, target_result in results.items():
        suite = junit.TestSuite(platform + target)
        for case_name, case_result in target_result.items():
            case = junit.TestCase(case_name)
            if case_result["status"] == "FAIL":
                case.result = junit.Failure(case_result.get("details", ""))
            if case_result["status"] == "IGNORE":
                case.result = junit.Skipped(case_result.get("details", ""))
            suite.add_testcase(case)
        report.add_testsuite(suite)
    report.update_statistics()

    return report


def write_junit(junit_report, file_name):
    try:
        junit_report.write(file_name, pretty=True)
    except Exception as err:
        print(f"[ERROR] Unable to write junit_file: {str(err)}")


def check_doxygen_warnings(results, abs_lib_path, lib_dir):
    """
    Prints the Doxygen warnings found from running the configuration file in the
    library under the abs_lib_paths. Returns the number of warnings if there are
    any.
    """
    # Setup junit results.
    target_result = results.setdefault(lib_dir, {})
    target_doxygen_result = target_result.setdefault("Doxygen warnings", {})

    os.chdir(abs_lib_path)
    out = run_cmd(f"doxygen docs/doxygen/config.doxyfile")
    print(out)
    if out.count("\n") > 0:
        target_doxygen_result["status"] = "FAIL"
        target_doxygen_result["details"] = "Doxygen warnings were output."
    else:
        target_doxygen_result["status"] = "PASS"


def check_doxygen_config_match(results, abs_lib_path, lib_dir):
    """
    Check the Doxygen configs are the same as the hub, except for lines 
    containing "FIXME".
    """
    # Setup junit results.
    target_result = results.setdefault(lib_dir, {})
    target_doxygen_result = target_result.setdefault("Doxygen config match", {})

    # Open the Doxygen config files for processing.
    lib_doxy_files_path = os.path.join(abs_lib_path, "docs", "doxygen")
    template_config_file = open(os.path.join(DOXYGEN_TEMPLATES_PATH, DOXYGEN_CONFIG_FILE), "r")
    lib_config_file = open(os.path.join(lib_doxy_files_path, DOXYGEN_CONFIG_FILE), "r")

    # Some Doxygen configs are on multiple lines, but it is easier to match
    # a single line. For a multiple line configuration, the probability of
    # the doc writer mis-configuring the subsequent lines is extremely low.
    # If we match the first line it gives us a good enough picture of the
    # configuration being present in a good condition or not.
    regex = re.compile("^[A-Z].*", re.MULTILINE)
    template_configs = regex.findall(template_config_file.read())
    lib_configs = regex.findall(lib_config_file.read())

    # Trim all of the white spaces, get rid of configs with no settings, and get
    # rid of configurations with FIXMEs.
    template_configs = set(
        filter(
            lambda config: all(custom_config not in config for custom_config in DOXYGEN_ALLOWED_CUSTOM_CONFIGS),
            filter(lambda config: config[-1] != "=", map(lambda config: config.replace(" ", ""), template_configs)),
        )
    )
    lib_configs = set(
        filter(lambda config: config[-1] != "=", map(lambda config: config.replace(" ", ""), lib_configs))
    )

    # Get all of the mismatched configs in the library.
    mismatched_configs = template_configs.difference(lib_configs)

    if len(mismatched_configs) == 0:
        target_doxygen_result["status"] = "PASS"
    else:
        target_doxygen_result["status"] = "FAIL"
        target_doxygen_result["details"] = f"The Doxygen configurations are mismatched: {mismatched_configs}."


def check_doxygen_style_match(results, abs_lib_path, lib_dir):
    """
    Check the Doxygen style.css and layout.xml are the same as the hub.
    """
    target_result = results.setdefault(lib_dir, {})
    target_doxygen_result = target_result.setdefault("Doxygen template match", {})

    lib_doxy_files_path = os.path.join(abs_lib_path, "docs", "doxygen")
    for template_file in DOXYGEN_STYLE_FILES:
        lib_doxy_file_path = os.path.join(lib_doxy_files_path, template_file)
        template_file_path = os.path.join(DOXYGEN_TEMPLATES_PATH, template_file)
        if os.path.exists(lib_doxy_file_path):
            same = filecmp.cmp(template_file_path, lib_doxy_file_path)
            if same == False:
                target_doxygen_result["status"] = "FAIL"
                target_doxygen_result["details"] = f"Template file {template_file} is different."
            else:
                target_doxygen_result["status"] = "PASS"
        else:
            target_doxygen_result["status"] = "FAIL"
            target_doxygen_result["details"] = f"Template file {template_file} is missing."


def check_transport_interface_match(results, abs_lib_path, lib_dir):
    """
    Check that the transport_interface.h in this library path is the same as the
    one in the hub.
    """
    target_result = results.setdefault(lib_dir, {})
    target_transport_result = target_result.setdefault("Transport interface match", {})

    lib_transport_interface_path = os.path.join(abs_lib_path, "source", "portable", "transport_interface.h")
    # All lines except the second where the library/SDK name and version are will
    # need to match.
    line_count = 0
    lib_file = open(lib_transport_interface_path, "r")
    lib_lines = lib_file.readlines()
    csdk_file = open(TRANSPORT_INTERFACE_PATH, "r")
    csdk_lines = csdk_file.readlines()
    same = True
    for line in lib_lines:
        line_count = line_count + 1
        if line_count == 2:
            continue
        if line != csdk_lines[line_count - 1]:
            same = False
            break

    if same == False:
        target_transport_result["status"] = "FAIL"
        target_transport_result[
            "details"
        ] = f"transport_interface.h is different. Different at line {line_count}: {lib_lines[line_count]}"
    else:
        target_transport_result["status"] = "PASS"


def get_abs_lib_paths(root):
    """
    Get all of the paths to the libraries under the standard and aws library
    folders.
    """
    standard_libs_path = os.path.join(root, "libraries", "standard")
    aws_libs_path = os.path.join(root, "libraries", "aws")
    abs_lib_paths = []

    lib_dirs = os.listdir(standard_libs_path)
    abs_lib_paths += list(map(lambda lib_dir: os.path.join(standard_libs_path, lib_dir), lib_dirs))
    lib_dirs = os.listdir(aws_libs_path)
    abs_lib_paths += list(map(lambda lib_dir: os.path.join(aws_libs_path, lib_dir), lib_dirs))
    return abs_lib_paths


def main():
    """
    This script checks the doxygen warnings and that template files are the same
    across all of the library submodules.
    This script should be run in the root of the CSDK repo.
    """
    global DOXYGEN_TEMPLATES_PATH
    global TRANSPORT_INTERFACE_PATH

    root = os.path.abspath(".")
    DOXYGEN_TEMPLATES_PATH = os.path.join(root, DOXYGEN_TEMPLATES_PATH)
    TRANSPORT_INTERFACE_PATH = os.path.join(root, TRANSPORT_INTERFACE_PATH)

    # Get the absolute paths to all of the libraries in the CSDK.
    abs_lib_paths = get_abs_lib_paths(root)

    results = {}
    # Get the issues in the spoke repos:
    for abs_lib_path in abs_lib_paths:
        lib_dir = os.path.basename(abs_lib_path)
        if os.path.exists(os.path.join(abs_lib_path, "docs", "doxygen")):
            check_doxygen_warnings(results, abs_lib_path, lib_dir)
            check_doxygen_style_match(results, abs_lib_path, lib_dir)
            check_doxygen_config_match(results, abs_lib_path, lib_dir)
        if os.path.exists(os.path.join(abs_lib_path, "source", "portable", "transport_interface.h")):
            check_transport_interface_match(results, abs_lib_path, lib_dir)

    # Get the warnings in this hub repo (CSDK). This is done last to acquire the
    # tags generated in the spoke library repos.
    check_doxygen_warnings(results, root, "CSDK")

    write_junit(to_junit(results, ""), os.path.join(root, "doxygen.xml"))


if __name__ == "__main__":
    main()
