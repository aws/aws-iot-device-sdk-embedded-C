# Pre-release verification for AWS IoT Embedded C SDK

## Prerequisites

- Linux environment
- [Git](https://git-scm.com/downloads/)
- [Python 3](https://www.python.org/downloads/)
- See [requirements.txt](requirements.txt) for the versions of Python packages needed.

This script accompanies the CSDK release CM. You must use it in conjunction with a Preflight step.

## Output
This script checks that:
    - All unit tests and code quality checks pass in each library repo committed on the main branch.
    - All jobs pass in <JENKINS_CI_URL>/view/CSDK%20Jobs/job/csdk/
    - Only the main branch exists in library repos.
    - Only the main branch and v4_beta_deprecated exist in the CSDK.
    - Each library repo has a tag and release labeled with the version specified in the config.
    - manifest.yml has all libraries and versions expected in this script's config.yml
    - There are no pending PRs on the main branch.

This script outputs:
    - **error.log** in the working directory for any errors found in verification.
    - **docs_to_review.txt** for all CHANGELOG.md and README.md files that need manual review.

## Usage

1. Clone https://github.com/aws/aws-iot-device-sdk-embedded-C/
```console
git clone git@github.com:aws/aws-iot-device-sdk-embedded-C.git --recurse-submodules
```

1. You will need your [Github API Access Token](https://docs.github.com/en/free-pro-team@latest/github/authenticating-to-github/creating-a-personal-access-token) and Jenkins CI URL, Username and Password. These should be saved into your system's environment variables as GITHUB_ACCESS_TOKEN, JENKINS_USERNAME, JENKINS_PASSWORD, JENKINS_API_URL.
```console
export GITHUB_ACCESS_TOKEN="my-secret-github-access-token"
export JENKINS_API_URL="aws-team-jenkins-url"
export JENKINS_USERNAME="my-jenkins-ci-username"
export JENKINS_PASSWORD="my-jenkins-ci-password"
```
You can also enter these as parameters to the script.
```
--github-access-token "my-secret-github-access-token"
--jenkins-api-url "aws-team-jenkins-url"
--jenkins-user "my-jenkins-ci-username"
--jenkins-password "my-jenkins-ci-password"
```

1. Run the script with the versions of every library repo that exists under [libraries/aws](../../libraries/aws) and [libaries/standard](../../libraries/standard) directories.
```console
python3 tools/release/release-verify.py \
--root aws-iot-device-sdk-embedded-c \
--csdk-version <CSDK_VERSION> \
--coremqtt-version <MQTT_VERSION> \
--corehttp-version <HTTP_VERSION>  \
--corejson-version <JSON_VERSION>  \
--device-defender-for-aws-iot-embedded-sdk-version <DEFENDER_VERSION> \
--device-shadow-for-aws-iot-embedded-sdk-version <SHADOW_VERSION> \
--jobs-for-aws-iot-embedded-sdk-version <JOBS_VERSION> \
--corepkcs11-version <PKCS11_VERSION> \
--backoffalgorithm-version <BACKOFF_ALGORITHM_VERSION> \
--ota-for-aws-iot-embedded-sdk <OTA_LIBRARY_VERSION> \
--disable-cbmc-checks-for <LIBRARY1> \
--disable-cbmc-checks-for <LIBRARY2> \
--disable-jenkins-server-verify
```

