#!/usr/bin/env python3
#
# Python script for preparing the code base for the CBMC proofs.
#
# Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import argparse
import logging
import os
import pathlib
import subprocess
import sys
import textwrap

from make_cbmc_batch_files import create_cbmc_yaml_files

################################################################
# Argument parsing

def command_line_arguments():
    """Define command line arguments."""

    parser = argparse.ArgumentParser(
        description='Prepare MQTT source tree for CBMC proofs.'
    )

    parser.add_argument(
        '--patches',
        action='store_true',
        default=True,
        help='Apply patches to MQTT source tree to run proofs.'
    )
    parser.add_argument(
        '--no-patches',
        action='store_false',
        dest='patches',
        help='Apply patches to MQTT source tree to run proofs.'
    )
    parser.add_argument(
        '--yamls',
        action='store_true',
        default=True,
        help='Generate cbmc-batch.yaml files to run proofs in CI.'
    )
    parser.add_argument(
        '--no-yamls',
        action='store_false',
        dest='yamls',
        help='Generate cbmc-batch.yaml files to run proofs in CI.'
    )

    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Verbose output.'
    )
    parser.add_argument(
        '--debug',
        action='store_true',
        help='Debugging output.'
    )

    args = parser.parse_args()

    # Only the first invocation of basicConfig configures the root logger
    if args.debug:
        logging.basicConfig(
            level=logging.DEBUG,
            format="{script}: %(levelname)s %(message)s".format(
                script=os.path.basename(__file__)))
    if args.verbose:
        logging.basicConfig(
            level=logging.INFO,
            format="{script}: %(levelname)s %(message)s".format(
                script=os.path.basename(__file__)))
    logging.basicConfig(format="{script}: %(levelname)s %(message)s".format(
        script=os.path.basename(__file__)))

    return args

################################################################

def apply_patches():
    patch_dir = pathlib.Path(__file__).resolve().parent.parent / "patches"
    if not patch_dir.is_dir():
        logging.error("Patches directory at '%s' is not a directory", patch_dir)
        sys.exit(1)

    proj_dir = pathlib.Path(__file__).resolve().parent.parent.parent
    if not proj_dir.is_dir():
        logging.error("Root of project at '%s' is not a directory", proj_dir)
        sys.exit(1)
    if not (proj_dir / "LICENSE").exists():
        logging.error(
            "Directory '%s' doesn't seem to be root of project", proj_dir)
        sys.exit(1)

    for fyle in sorted(patch_dir.glob("*.patch")):
        logging.info("Checking patch '%s'", fyle.name)
        cmd = ["git", "apply", "--check", str(fyle)]
        proc = subprocess.run(
            cmd, cwd=str(proj_dir),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            universal_newlines=True)
        if proc.returncode:
            logging.warning(
                "Patch checking failed. Check output:\n%s",
                "\n".join(["    %s" % line for line in proc.stdout.splitlines()]))

        logging.info("Applying patch '%s'", fyle.name)
        cmd = ["git", "apply", str(fyle)]
        proc = subprocess.run(cmd, cwd=str(proj_dir))
        if proc.returncode:
            logging.error("Failed to apply patch '%s'", fyle.name)
            sys.exit(1)


def build():
    try:
        create_cbmc_yaml_files()
    except subprocess.CalledProcessError as error:
        logging.error(textwrap.dedent("""\
            An error occured during cbmc-batch generation.
            The error message is: {}
            """.format(str(error))))
        exit(1)

################################################################

def main():
    args = command_line_arguments()

    if args.yamls:
        build()
    if args.patches:
        apply_patches()

if __name__ == '__main__':
    main()
