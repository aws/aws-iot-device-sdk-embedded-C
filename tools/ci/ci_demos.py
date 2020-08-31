import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

import junitparser as junit
import yaml


def cli_config_build(args):
    _file = Path(args.config_file)
    _config = _read_config(_file)
    _build_flags = _config.get("_default", {}).get("build_flags", [])

    _del_dir(args.build_path)
    _config_build(args.src, _build_flags, args.build_path)


def cli_get_targets(args):
    _targets = _get_targets(args.build_path)
    print(" ".join(_targets))


def cli_build_targets(args):
    _file = Path(args.config_file)
    _config = _read_config(_file)
    result = _build_targets(args.targets, _config, args.build_path)

    _junit_filename = _config.get("_default", {}).get("name", None)
    if _junit_filename:
        _junit_filename = f"build_{_junit_filename}.xml"

    _log_save_result(result, _junit_filename)
    _check_status(result)


def cli_build(args):
    _file = Path(args.config_file)
    _config = _read_config(_file)
    _build_flags = _config.get("_default", {}).get("build_flags", [])

    _config_build(args.src, _build_flags, args.build_path)
    _targets = _get_targets(args.build_path)

    allowed = "|".join(_config.get("_default", {}).get("allow", []))
    _targets = [_target for _target in _targets if re.match(allowed, _target)]

    result = _build_targets(_targets, _config, args.build_path)

    _junit_filename = _config.get("_default", {}).get("name", None)
    if _junit_filename:
        _junit_filename = f"build_{_junit_filename}.xml"

    _log_save_result(result, _junit_filename)
    _check_status(result)


def cli_invoke(args_list):
    _cli_invoke_next(args_list)


def get_parser():
    def new_argument(arg, **kwargs):
        arguments[arg] = kwargs

    def add_argument(cmd, arg, **kwargs):
        cmd.add_argument(arg, **{**arguments.get(arg, {}), **kwargs})

    def add_arguments(cmd, *args):
        for arg in args:
            cmd.add_argument(arg, **arguments[arg])

    arguments = {}
    new_argument("--src", required=True, help="Path to C-SDK")
    new_argument("--config-file", default=".", help="Path to config file")
    new_argument("--build-path", required=True, help="Path to build location")
    new_argument(
        "--build-args", default="", help="Arguments required for build configuration"
    )
    new_argument("--targets", nargs="+", required=True, help="Targets to build")

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers()

    cmd_config_build = subparsers.add_parser("configure-build")
    add_arguments(
        cmd_config_build, "--config-file", "--src", "--build-path", "--build-args"
    )
    cmd_config_build.set_defaults(func="config-build")

    cmd_get_targets = subparsers.add_parser("get-targets")
    add_argument(cmd_get_targets, "--build-path")
    cmd_get_targets.set_defaults(func="get-targets")

    cmd_build_targets = subparsers.add_parser("build-targets")
    add_arguments(cmd_build_targets, "--config-file", "--targets", "--build-path")
    cmd_build_targets.set_defaults(func="build-targets")

    cmd_build = subparsers.add_parser("build")
    add_arguments(cmd_build, "--config-file", "--src", "--build-path", "--build-args")
    cmd_build.set_defaults(func="build")
    return parser


def main():
    parser = get_parser()
    if len(sys.argv) <= 1:
        parser.print_help()
        sys.exit(1)

    args_list = parser.parse_args()
    cli_invoke(args_list)


# -----------------------------------------------------------------------------------
# Private Functions
# -----------------------------------------------------------------------------------
def _cli_invoke_next(args_list, prefix="cli"):
    next_cmd = args_list.func
    args = args_list
    func = globals()[prefix + "_" + next_cmd.replace("-", "_")]
    func_args = [args] if vars(args) else [] + [args_list] if args_list else []
    return func(*func_args)


def _config_build(_src, _build_flags, _build_path):
    _build_flags = " ".join(_build_flags)
    _run_cmd(f'cmake -S {_src} -B {_build_path} {_build_flags}  -G "Unix Makefiles"')


def _build_target(_target, _c_flags, build_path):
    print("\n----------------------------------------------------------------")
    print(f"Building target: {_target}")
    print("----------------------------------------------------------------")
    _c_flags = " ".join(_c_flags)
    cmd = f"make -C {build_path} {_c_flags} {_target}"
    print(_run_cmd(cmd))


def _get_targets(build_path):
    _targets = _run_cmd(f"make help -C {build_path} | tr -d '. '")
    _targets = [_t.strip() for _t in _targets.split()]
    return _targets


def _build_targets(_targets, _config, build_path):
    result = {}

    for _target in _targets:
        _target_result = result.setdefault(_target, {})
        _target_build_result = _target_result.setdefault("Build", {})
        try:
            _c_flags = _config.get("_default", {}).get("c_flags", []) + _config.get(
                _target, {}
            ).get("c_flags", [])
            _build_target(_target, _c_flags, build_path)
            _target_build_result["status"] = "PASS"
        except subprocess.CalledProcessError as err:
            print(err.stdout)
            _target_build_result["status"] = "FAIL"
            _target_build_result["details"] = "Build Failure"
    return result


def _del_dir(dir_name):
    try:
        print(f"Deleting dir: {dir_name}")
        shutil.rmtree(dir_name)
    except OSError as err:
        print("Error: %s - %s." % (err.filename, err.strerror))


def _read_config(_path):
    try:
        _config = yaml.load(_path.read_text())
        return _config
    except yaml.YAMLError:
        print(f"Error: Unable to load file {_path.name}")
        sys.exit(1)


def _run_cmd(cmd):
    print(f"Executing command: {cmd}")
    result = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        shell=True,
        encoding="utf-8",
        check=True,
    )
    return result.stdout


def _check_status(result):
    status = any([_k for _k, _v in result.items() if _v.get("status") == "FAIL"])
    if status:
        sys.exit(1)


def _log_save_result(result, filename):
    print("\n----------------------------------------------------------------")
    print("Build Result")
    print("----------------------------------------------------------------")
    print(yaml.dump(result))

    if filename:
        _write_junit(_to_junit(result, "linux.cmake"), filename)


def _to_junit(result, platform=""):
    """
    Convert result to junit format.
    """
    report = junit.JUnitXml()
    if not result:
        return report

    platform += platform and "."

    for target, target_result in result.items():
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


def _write_junit(junit_report, file_name):
    try:
        junit_report.write(file_name, pretty=True)
    except Exception as err:
        print(f"[ERROR] Unable to write junit_file: {str(err)}")


if __name__ == "__main__":
    main()
