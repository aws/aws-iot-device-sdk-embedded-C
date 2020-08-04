import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import junitparser as junit
import requests
import yaml


def log(message):
    print(message)


def cli_config_build(args):
    _file = Path(args.config_file)
    config = _read_config(_file)
    build_flags = args.build_flags or _get_flags(config, "build_flags")
    c_flags = args.c_flags or _get_flags(config, "c_flags")

    _config_build(args.src, args.build_path, build_flags, c_flags)


def cli_get_targets(args):
    allow = args.allow or [""]
    targets = _get_targets(args.build_path, allow)
    log(" ".join(targets))


def cli_build_targets(args):
    _file = Path(args.config_file)
    config = _read_config(_file)
    default_config = config.get("_default", {})
    junit_filename = default_config.get("name", None)
    result = _build_targets(args.targets, args.src, args.build_path, config)

    _log_save_result(result, f"build_{junit_filename}.xml")
    _check_status(result)


def cli_run_targets(args):
    _file = Path(args.config_file)
    config = _read_config(_file)
    default_config = config.get("_default", {})
    junit_filename = default_config.get("name", None)

    result = _run_targets(args.targets, args.src, args.build_path, config)
    _log_save_result(result, f"run_{junit_filename}.xml")
    _check_status(result)


def cli_build(args):
    _file = Path(args.config_file)
    config = _read_config(_file)
    default_config = config.get("_default", {})
    junit_filename = default_config.get("name", None)

    build_flags = _get_flags(config, "build_flags")
    c_flags = _get_flags(config, "c_flags")
    _config_build(args.src, args.build_path, build_flags, c_flags)

    allowed = args.allow or default_config.get("allow", [""])
    targets = args.targets or _get_targets(args.build_path, allowed)

    build_result = _build_targets(targets, args.src, args.build_path, config)

    _log_save_result(build_result, f"build_{junit_filename}.xml")
    _check_status(build_result)


def cli_run(args):
    _file = Path(args.config_file)
    config = _read_config(_file)
    default_config = config.get("_default", {})
    junit_filename = default_config.get("name", None)

    build_flags = _get_flags(config, "build_flags")
    c_flags = _get_flags(config, "c_flags")
    _config_build(args.src, args.build_path, build_flags, c_flags)

    allowed = args.allow or default_config.get("allow", [""])
    targets = args.targets or _get_targets(args.build_path, allowed)

    result = _run_targets(targets, args.src, args.build_path, config)

    _log_save_result(result, f"run_{junit_filename}.xml")
    _check_status(result)


def cli_code_coverage(args):
    """
    Generates Code Coverage report.

    Create code coverage report using gcov.

    Parameters:
    src: location of csdk src
    build_path: location of build dir
    config_file: Specifies configuration for setting cmake build.
    build_flags: [Optional] Array of build flags to setup cmake build.
    c_flags: [Optional] Array of c flags used by compiler
    codecov_token: [Optional] codecov token required to upload code to codecov.io
    """

    _file = Path(args.config_file)
    config = _read_config(_file)
    default_config = config.get("_default", {})

    build_flags = args.build_flags or _get_flags(config, "build_flags")
    c_flags = args.c_flags or _get_flags(config, "c_flags")
    codecov_token = args.codecov_token or default_config.get("codecov_token", None)

    result = _build_code_coverage(
        args.src, args.build_path, build_flags, c_flags, codecov_token
    )
    _log_save_result(result, f"build_coverage.xml")
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
    new_argument("--targets", nargs="+", required=True, help="Targets to build")
    new_argument(
        "--build-flags", nargs="+", help="Optional flags required to configure build",
    )
    new_argument(
        "--c-flags", nargs="+", help="Optional c_flags required to configure build",
    )
    new_argument("--allow", nargs="+", help="Pattern for target selection")
    new_argument(
        "--codecov-token", help="Optional token to upload coverage report to codecov.io"
    )

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers()

    cmd_config_build = subparsers.add_parser("configure-build")
    add_arguments(
        cmd_config_build,
        "--config-file",
        "--src",
        "--build-path",
        "--build-flags",
        "--c-flags",
    )
    cmd_config_build.set_defaults(func="config-build")

    cmd_get_targets = subparsers.add_parser("get-targets")
    add_arguments(cmd_get_targets, "--build-path", "--allow")
    cmd_get_targets.set_defaults(func="get-targets")

    cmd_build_targets = subparsers.add_parser("build-targets")
    add_arguments(
        cmd_build_targets, "--src", "--config-file", "--targets", "--build-path"
    )
    cmd_build_targets.set_defaults(func="build-targets")

    cmd_run_targets = subparsers.add_parser("run-targets")
    add_arguments(
        cmd_run_targets, "--src", "--config-file", "--targets", "--build-path"
    )
    cmd_run_targets.set_defaults(func="run-targets")

    cmd_build = subparsers.add_parser("build")
    add_arguments(
        cmd_build, "--config-file", "--src", "--build-path", "--build-flags", "--allow"
    )
    add_argument(cmd_build, "--targets", required=False)
    cmd_build.set_defaults(func="build")

    cmd_run = subparsers.add_parser("run")
    add_arguments(
        cmd_run, "--config-file", "--src", "--build-path", "--build-flags", "--allow"
    )
    add_argument(cmd_run, "--targets", required=False)
    cmd_run.set_defaults(func="run")

    cmd_code_coverage = subparsers.add_parser("code-coverage")
    add_arguments(
        cmd_code_coverage,
        "--config-file",
        "--src",
        "--build-path",
        "--build-flags",
        "--c-flags",
        "--codecov-token",
    )
    cmd_code_coverage.set_defaults(func="code-coverage")

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


def _config_build(src, build_path, build_flags, c_flags):
    build_flags = " ".join(build_flags)
    c_flags = " ".join(c_flags).replace("'", '"').replace('"', '\\"')
    c_flags = f"-DCMAKE_C_FLAGS='{c_flags}'"
    _del_dir(build_path)
    _run_cmd(
        f'cmake -S {src} -B {build_path} {build_flags} {c_flags} -G "Unix Makefiles"'
    )


def _get_flags(config, flag_type, target="all"):
    targets = config.keys() if target == "all" else ["_default", target]

    flags = []
    for _target in targets:
        flags += config.get(_target, {}).get(flag_type, [])
    return flags


def _get_targets(build_path, allow):
    targets = _run_cmd(f"make help -C {build_path} | tr -d '. '")
    targets = [t.strip() for t in targets.split()]
    allow = "|".join(allow)
    targets = [target for target in targets if re.search(allow, target)]
    return targets


def _build_target(target, src, build_path, build_flags, c_flags):
    log("\n----------------------------------------------------------------")
    log(f"Building target: {target}")
    log("----------------------------------------------------------------")

    _config_build(src, build_path, build_flags, c_flags)

    cmd = f"make -C {build_path} {target}"
    return _run_cmd(cmd)


def _build_targets(targets, src, build_path, config):
    result = {}

    for target in targets:
        target_result = result.setdefault(target, {})
        target_build_result = target_result.setdefault("Build", {})
        try:
            build_flags = _get_flags(config, "build_flags", target)
            c_flags = _get_flags(config, "c_flags", target)
            out = _build_target(target, src, build_path, build_flags, c_flags)
            log(out)
            target_build_result["status"] = "PASS"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as err:
            log(err.stdout)
            target_build_result["status"] = "FAIL"
            target_build_result["details"] = "Build Failure"
    return result


def _run_target(target, run_path):
    log("\n----------------------------------------------------------------")
    log(f"Running Target: {target}")
    log("----------------------------------------------------------------")
    return _run_cmd(f"cd {run_path} && ./{target}")


def _run_targets(targets, src, build_path, config):
    result = {}
    default_config = config.get("_default", {})
    for target in targets:
        target_result = result.setdefault(target, {})

        target_build_result = target_result.setdefault("Build", {})
        try:
            build_flags = _get_flags(config, "build_flags", target)
            c_flags = _get_flags(config, "c_flags", target)
            out = _build_target(target, src, build_path, build_flags, c_flags)
            log(out)
            target_build_result["status"] = "PASS"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as err:
            log(err.stdout)
            target_build_result["status"] = "FAIL"
            target_build_result["details"] = "Build Failure"

        target_run_result = target_result.setdefault("Run", {})
        run_path = f'{build_path}/{default_config.get("output_loc", "")}'
        try:
            out = _run_target(target, run_path)
            log(out)
            target_run_result["status"] = "PASS"
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as err:
            log(err.stdout)
            target_run_result["status"] = "FAIL"
            target_run_result["details"] = "Run Failure"
    return result


def _build_code_coverage(src, build_path, build_flags, c_flags, codecov_token):
    """
    Private code coverage function.

    Parameters:
    src: location of csdk src
    build_path: location of build dir
    build_flags: Array of build flags to setup cmake build.
    c_flags: Array of c flags used by compiler
    codecov_token: codecov token required to upload code to codecov.io
    """
    result = {}
    try:
        target_result = result.setdefault("coverage", {})
        target_build_result = target_result.setdefault("CodeCoverage", {})
        out = _build_target("coverage", src, build_path, build_flags, c_flags)
        log(out)
        out = _run_cmd(f"gcovr -r . -x -o {build_path}/cobertura.xml")
        log(out)

        commit_id = os.environ.get("ghprbActualCommit") or ""

        if codecov_token and commit_id:
            log("\n----------------------------------------------------------------")
            log("Upload Code Coverage report to codecov.io")
            log("----------------------------------------------------------------")

            params = {
                "token": codecov_token,
                "commit": commit_id,
                "branch": "",
                "build": "",
                "build_url": "",
                "name": "",
                "tag": "",
                "slug": "",
                "service": "",
                "flags": "",
                "pr": "",
                "job": "",
                "cmd_args": "",
            }
            headers = {"content-type": "application/x-www-form-urlencoded"}
            with open(f"{build_path}/cobertura.xml", "rb") as payload:
                try:
                    requests.post(
                        "https://codecov.io/upload/v2",
                        data=payload,
                        verify=True,
                        headers=headers,
                        params=params,
                    )
                except requests.exceptions.RequestException as err:
                    log(f"Error calling codecov.io: {err}")
        else:
            if not commit_id:
                log(
                    "Please provide commit id, if you want to upload coverage report to codecov.io"
                )
            if not codecov_token:
                log(
                    "Provide '--codecov-token' in commandline, \
                    if you want to upload coverage report to codecov.io"
                )
        target_build_result["status"] = "PASS"
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as err:
        log(err.stdout)
        target_build_result["status"] = "FAIL"
        target_build_result["details"] = "Code Coverage Failure"
    return result


def _del_dir(dir_name):
    try:
        log(f"Deleting dir: {dir_name}")
        shutil.rmtree(dir_name)
    except OSError as err:
        log("Error: %s - %s." % (err.filename, err.strerror))


def _read_config(_path):
    try:
        _config = yaml.load(_path.read_text())
        return _config
    except yaml.YAMLError:
        log(f"Error: Unable to load file {_path.name}")
        sys.exit(1)


def _run_cmd(cmd):
    log(f"Executing command: {cmd}")
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


def _check_status(result):
    status = any(
        [
            _k
            for _k, _v in result.items()
            for _k1, _v1 in _v.items()
            if not _v1.get("status") == "PASS"
        ]
    )
    if status:
        sys.exit(1)


def _log_save_result(result, filename):
    log("\n----------------------------------------------------------------")
    log(f"{filename.split('_')[0].title()} Result")
    log("----------------------------------------------------------------")
    log(yaml.dump(result))

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
        log(f"[ERROR] Unable to write junit_file: {str(err)}")


if __name__ == "__main__":
    main()
