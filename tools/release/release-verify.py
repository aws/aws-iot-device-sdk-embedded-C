#!/usr/bin/env python3
import subprocess
import argparse
import os
import yaml
import requests
import logging
from requests.auth import HTTPBasicAuth
import re

# Directories where the library submodules exist.
CSDK_LIBRARY_DIRS = ["libraries/aws", "libraries/standard"]

# CSDK organization and repo constants
CSDK_ORG = "aws"
CSDK_REPO = "aws-iot-device-sdk-embedded-c"

# Github API global. The Github API is used instead of pyGithub because some
# checks are not available yet in the package.
GITHUB_API_URL = "https://api.github.com"
GITHUB_ACCESS_TOKEN = ""
GITHUB_AUTH_HEADER = {"Authorization": "token {}", "Accept": "application/vnd.github.v3+json"}

# Jenkins API globals
JENKINS_API_URL = ""
JENKINS_USERNAME = ""
JENKINS_PASSWORD = ""
JENKINS_CSDK_DEMOS_PATH = "job/csdk/job/demo_pipeline/lastCompletedBuild"
JENKINS_CSDK_TESTS_PATH = "job/csdk/job/nightly/lastCompletedBuild"
JENKINS_API_PATH = "api/json"
JENKINS_SERVER_VERIFY = True
GITHUB_RELEASES_TAGS_VERIFY = True

# Errors found in this run.
errors = 0

def log_error(error_log):
    """
    Logs an error to error.log.
    Args:
        error_log (str): Error string to log.
    """
    global errors
    logging.error(error_log)
    errors = errors + 1


def validate_manifest(csdk_root, csdk_version, lib_versions):
    """
    Validates the manifest.yml file at the root of the CSDK.
    Args:
        csdk_root (str): The root path to the CSDK repo.
        csdk_versions (str): The new version of the CSDK repo.
        lib_versions (dict): A dictionary containing the new versions of each library.
        Please see tools/release/config.yml.
    """
    with open(os.path.join(csdk_root, "manifest.yml")) as manifest_file:
        manifest = yaml.load(manifest_file, Loader=yaml.FullLoader)

    # Verify the CSDK version is correct.
    manifest_version = manifest["version"]
    if manifest_version != csdk_version:
        log_error(f"Invalid manifest.yml. CSDK version {manifest_version} should be {csdk_version}.")

    # Verify that all libraries in this branch are also in the manifest.yml.
    for library_dir in CSDK_LIBRARY_DIRS:
        libraries = os.listdir(os.path.join(csdk_root, library_dir))
        for library in libraries:
            library = library.lower()
            found = filter(lambda dep: dep["name"].casefold() == library, manifest["dependencies"])
            found = list(found)
            if len(found) != 1:
                log_error(f"Invalid manifest.yml. Found {len(found)} occurrences of required library {library}.")
            else:
                dep_version = found[0]["version"]
                dep_name = found[0]["name"]
                if dep_version.lower() != lib_versions[library]:
                    log_error(f"Invalid manifest.yml. Invalid version {dep_version} for {dep_name}.")


def validate_checks(configs) -> list:
    """
    Validates that all of the GHA and CBMC status checks passed on all repos.
    Returns a list of existing org/repo paths found.
    """
    docs_file = open("docs_to_review.txt", "w+")
    repo_paths = []
    for library_dir in CSDK_LIBRARY_DIRS:
        # Get the submodules in the library directory.
        git_resp = requests.get(
            f"{GITHUB_API_URL}/repos/{CSDK_ORG}/{CSDK_REPO}/contents/{library_dir}?ref=main",
            headers=GITHUB_AUTH_HEADER,
        )
        # A 404 status code means the branch doesn't exist.
        if git_resp.status_code == 404:
            log_error(
                "The main branch does not exist in the CSDK. Please recheck the branches in the repo."
            )
            break
        else:
            # For each library submodule in this directory, get the status checks results and docs to review.
            for library in git_resp.json():
                library_name = library["name"]
                # Get the commit SHA of the branch currently in main.
                commit_sha = library["sha"]
                # Get the organization of this repo
                html_url = library["html_url"]
                repo_path = re.search("(?<=\.com/)(.*)(?=/tree)", html_url).group(0)
                repo_paths.append(repo_path)

                # Verify CBMC checks for the libraries not excluded.
                if library_name.lower() not in configs["libraries-to-disable-cbmc-checks"]:
                    # Get the status of the CBMC checks
                    git_resp = requests.get(
                        f"{GITHUB_API_URL}/repos/{repo_path}/commits/{commit_sha}/status", headers=GITHUB_AUTH_HEADER
                    )
                    if git_resp.json()["state"] != "success":
                        log_error(f"The CBMC status checks failed for {html_url}.")

                # Get the status of the GHA checks
                git_resp = requests.get(
                    f"{GITHUB_API_URL}/repos/{repo_path}/commits/{commit_sha}/check-runs", headers=GITHUB_AUTH_HEADER
                )
                for check_run in git_resp.json()["check_runs"]:
                    if check_run["conclusion"] != "success":
                        check_run_name = check_run["name"]
                        log_error(f"The GHA {check_run_name} check failed for {html_url}.")

                # Collect the HTML URLS for reviewing the docs.
                html_url = html_url.split(commit_sha)[0] + "main"
                docs_file.write(f"{library_name}\n")
                docs_file.write(f"{html_url}/README.md\n")
                docs_file.write(f"{html_url}/CHANGELOG.md\n\n")

    docs_file.close()
    repo_paths.append(f"{CSDK_ORG}/{CSDK_REPO}")
    return repo_paths

def validate_ci():
    """
    Validates that all CSDK jobs in the Jenkins CI passed.
    """
    jenkins_resp = requests.get(
        f"{JENKINS_API_URL}/{JENKINS_CSDK_DEMOS_PATH}/{JENKINS_API_PATH}",
        auth=HTTPBasicAuth(JENKINS_USERNAME, JENKINS_PASSWORD),
        verify=JENKINS_SERVER_VERIFY,
    )
    if jenkins_resp.json()["result"] != "SUCCESS":
        log_error(f"Jenkins job failed: {JENKINS_API_URL}/{JENKINS_CSDK_DEMOS_PATH}.")
    jenkins_resp = requests.get(
        f"{JENKINS_API_URL}/{JENKINS_CSDK_TESTS_PATH}/{JENKINS_API_PATH}",
        auth=HTTPBasicAuth(JENKINS_USERNAME, JENKINS_PASSWORD),
        verify=JENKINS_SERVER_VERIFY,
    )
    if jenkins_resp.json()["result"] != "SUCCESS":
        log_error(f"Jenkins job failed: {JENKINS_API_URL}/{JENKINS_CSDK_TESTS_PATH}.")


def validate_branches(repo_paths):
    """
    Validates that only the main branch exists on each library repo.
    Args:
        repo_paths (dict): Paths to all library repos in the CSDK, including their org.
    """
    for repo_path in repo_paths:
        git_resp = requests.get(f"{GITHUB_API_URL}/repos/{repo_path}/branches", headers=GITHUB_AUTH_HEADER)
        valid_branches = ["main"]
        if repo_path == f"{CSDK_ORG}/{CSDK_REPO}":
            valid_branches += ["v4_beta_deprecated"]
        for branch in git_resp.json():
            branch_name = branch["name"]
            if branch_name not in valid_branches:
                log_error(f"Invalid branch {branch_name} found in {repo_path}.")

def validate_tags_and_releases(repo_paths, lib_versions):
    """
    Validates that each library repo has a release and tag for the specified version number.
    Args:
        repo_paths (dict): Paths to all library repos in the CSDK, including their org.
        lib_versions (dict): A dictionary containing the new versions of each library.
    """
    if not GITHUB_RELEASES_TAGS_VERIFY:
        return
    # Verify that all repos have a release and tag for the version specified in the config.
    for repo_path in repo_paths:
        library = repo_path.split("/")[-1].casefold()
        # Only need to verify for spoke repos because CSDK is the library being released.
        if library == CSDK_REPO:
            continue
        # Check that a release exists with the same name as the version.
        git_releases_resp = requests.get(f"{GITHUB_API_URL}/repos/{repo_path}/releases", headers=GITHUB_AUTH_HEADER)
        found_release_for_version = False
        for release in git_releases_resp.json():
            if release["name"] == lib_versions[library] and release["tag_name"] == lib_versions[library]:
                found_release_for_version = True
                break
        if not found_release_for_version:
            log_error(f"Could not find release {lib_versions[library]} for {repo_path}.")
        # Check that a tag exists with the same name as the version.
        git_tags_resp = requests.get(f"{GITHUB_API_URL}/repos/{repo_path}/tags", headers=GITHUB_AUTH_HEADER)
        found_tag_for_version = False
        for tag in git_tags_resp.json():
            if tag["name"] == lib_versions[library]:
                found_tag_for_version = True
                break
        if not found_tag_for_version:
            log_error(f"Could not find tag {lib_versions[library]} for {repo_path}.")

def validate_main_branch():
    """
    Verifies there are no pending PRs to the main branch.
    """
    git_resp = requests.get(
        f"{GITHUB_API_URL}/repos/{CSDK_ORG}/{CSDK_REPO}/pulls?base=main", headers=GITHUB_AUTH_HEADER
    )
    if len(git_resp.json()) == 0:
        logging.warning("main branch does not exist in CSDK.")
    for pr in git_resp.json():
        if not pr["draft"]:
            pr_url = pr["url"]
            log_error(f"Pull request to main {pr_url}.")

def set_globals(configs):
    """
    Set global variables used in this script.
    Args:
        configs (dict): User configurations for this script.
    """
    global GITHUB_ACCESS_TOKEN
    global GITHUB_AUTH_HEADER
    global GITHUB_RELEASES_TAGS_VERIFY
    global JENKINS_API_URL
    global JENKINS_USERNAME
    global JENKINS_PASSWORD
    global JENKINS_SERVER_VERIFY

    access_token = os.environ.get("GITHUB_ACCESS_TOKEN")
    if access_token == None:
        access_token = configs["github_access_token"]
    if access_token == None:
        raise Exception(
            "Please define GITHUB_ACCESS_TOKEN in your system's environment variables or pass argument --github-access-token to this script."
        )
    jenkins_username = os.environ.get("JENKINS_USERNAME")
    if jenkins_username == None:
        jenkins_username = configs["jenkins_username"]
    if jenkins_username == None:
        raise Exception(
            "Please define JENKINS_USERNAME in your system's environment variables or pass argument --jenkins-username to this script."
        )
    jenkins_password = os.environ.get("JENKINS_PASSWORD")
    if jenkins_password == None:
        jenkins_password = configs["jenkins_password"]
    if jenkins_password == None:
        raise Exception(
            "Please define JENKINS_PASSWORD in your system's environment variables or pass argument --jenkins-password to this script."
        )
    jenkins_api_url = os.environ.get("JENKINS_API_URL")
    if jenkins_api_url == None:
        jenkins_password = configs["jenkins_api_url"]
    if jenkins_password == None:
        raise Exception(
            "Please define JENKINS_API_URL in your system's environment variables or pass argument --jenkins_api_url to this script."
        )
    GITHUB_ACCESS_TOKEN = access_token
    GITHUB_AUTH_HEADER["Authorization"] = GITHUB_AUTH_HEADER["Authorization"].format(GITHUB_ACCESS_TOKEN)
    JENKINS_USERNAME = jenkins_username
    JENKINS_PASSWORD = jenkins_password
    JENKINS_API_URL = jenkins_api_url
    JENKINS_SERVER_VERIFY = False if configs["disable_jenkins_server_verify"] else True
    GITHUB_RELEASES_TAGS_VERIFY = False if configs["disable_github_release_tag_verify"] else True


def get_configs() -> dict:
    """
    Parse the input user arguments and return a dictionary of arguments.
    """
    # Parse the input arguments to this script.
    parser = argparse.ArgumentParser(description="Perform CSDK Release activities.")
    parser.add_argument("-r", "--root", action="store", required=True, dest="root", help="CSDK repo root path.")
    parser.add_argument(
        "--github-access-token",
        action="store",
        required=False,
        dest="github_access_token",
        help="Github API developer access token.",
    )
    parser.add_argument(
        "--jenkins-api-url", action="store", required=False, dest="jenkins_api_url", help="Jenkins CI API url."
    )
    parser.add_argument(
        "--jenkins-username", action="store", required=False, dest="jenkins_username", help="Jenkins CI username."
    )
    parser.add_argument(
        "--jenkins-password", action="store", required=False, dest="jenkins_password", help="Jenkins CI password."
    )
    parser.add_argument(
        "--csdk-version", action="store", required=True, dest="csdk_version", help="CSDK version to be released."
    )
    parser.add_argument(
        "--disable-jenkins-server-verify",
        action="store_true",
        required=False,
        default=False,
        dest="disable_jenkins_server_verify",
        help="Disable server verification for the Jenkins API calls if your system doesn't have the certificate in its store.",
    )
    parser.add_argument(
        "--disable-github-release-tag-verify",
        action="store_true",
        required=False,
        default=False,
        dest="disable_github_release_tag_verify",
        help="Disable verifying that there are Github releases and tags named after the versions of the spoke repos.",
    )
    parser.add_argument(
        "--disable-cbmc-checks-for",
        action="append",
        required=False,
        default=[],
        dest="libraries-to-disable-cbmc-checks",
        type=str.lower,
        help="Disable CBMC checks for libraries, in case it is not available.",
    )

    args, unknown = parser.parse_known_args()
    csdk_root = os.path.abspath(args.root)

    # For each of the available libraries in the current branch require a version argument.
    for library_dir in CSDK_LIBRARY_DIRS:
        libraries = os.listdir(os.path.join(csdk_root, library_dir))
        for library in libraries:
            parser.add_argument(
                f"--{library.casefold()}-version",
                action="store",
                required=True,
                dest=f"{library.casefold()}",
                type=str.lower,
                help=f"{library} library version.",
            )
    args = parser.parse_args()
    configs = vars(args)
    return (configs, csdk_root)


def main():
    """
    Performs pre-release validation of the CSDK and the library spoke repos.
    """
    # Parse the input arguments and args for configurations and the  CSDK root.
    (configs, csdk_root) = get_configs()

    # Set the authentication variables.
    set_globals(configs)

    # Create error.log to write errors to.
    logging.basicConfig(filename="errors.log", filemode="w", level=logging.ERROR)

    # Verify that Manifest.yml has all libraries and their versions.
    validate_manifest(csdk_root, configs["csdk_version"], configs)

    # Verify status checks in all repos.
    repo_paths = validate_checks(configs)

    # Validate that the Jenkins CI passed.
    validate_ci()

    # Check that only qualified branches exist in each library repo.
    validate_branches(repo_paths)

    # Check that library repos have a tag and release for each specified version.
    validate_tags_and_releases(repo_paths, configs)

    # Verify there are no pending PRs to the CSDK main branch.
    validate_main_branch()

    if errors > 0:
        print("Release verification failed, please see errors.log")
    else:
        print("Release verification passed.")


if __name__ == "__main__":
    main()
