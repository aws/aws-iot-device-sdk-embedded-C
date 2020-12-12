# Link Verification Script

## Pre-Requisites

- Unix/Linux system
- Python3
- [pandoc](https://github.com/jgm/pandoc). Used to convert Markdown files to HTML, which are then searched.
- [GitHub CLI](https://github.com/cli/cli). Optional, but recommended to speed up the testing of links involving GitHub issues and pull requests.
- See [requirements.txt](requirements.txt) for versions of Python packages. This script uses beautfulsoup4, requests, and termcolor.

## Usage

```bash
python3 tools/link-verifier/verify-links.py -F [MARKDOWN_FILE_LIST] -L [URL_LIST]
```
The script will print URLs that were not accessible. For Markdown files, it will also test relative paths to files, and anchors within the same document.

### Allowlist

[allowlist.txt](allowlist.txt) contains a list of non-existant URLs used as placeholder examples in this repository. The script does not use it, but it can be used to filter out URLs before passing them in.

### Example
1. From the root of the repository, generate a list of Markdown files to test and store them in an array. Filter out files from third party repositories, and convert newlines to spaces.

```bash
FILES=($(find . -type f -name '*.md' | \
       grep -E -i -v 'cbmc|cmock|third-party|3rdparty|libmosquitto' | \
       tr '\n' ' '))
```
2. Extract URLs from the other files to test. Since Markdown files are tested separately, only search for `.c`, `.h`, and `.dox` files, and exclude directories from third party repositories. The URLs are sorted so that the allowlist can be used to filter them further.

```bash
LINKS=($(grep -e 'https\?://' . -RIa --include='*.c' --include='*.h' --include='*.dox' \
       --exclude-dir=.git --exclude-dir=cbmc --exclude-dir=CMock \
       --exclude-dir=third-party --exclude-dir=3rdparty --exclude-dir=libmosquitto | \
       grep -IoE '\b(https?|ftp|file)://[-A-Za-z0-9+&@#/%?=~_|!:,.;]*[-A-Za-z0-9+&@#/%=~_|]' | \
       sort | uniq | grep -Fxvf tools/link-verifier/allowlist.txt | tr '\n' ' '))
```
3. Run the script with the files and links. Optionally increase verbosity to print all links.

```bash
./tools/link-verifier/verify-links.py -F ${FILES[@]} -L ${LINKS[@]} -v
```

## Command Line Options

| Option | Argument | Description |
| --- | --- | --- |
| `-F`, `--files` | 1 or more space-separated filepaths | Filepaths to GitHub-flavored Markdown files for which to verify links. Filepaths may be absolute or relative. |
| `-L`, `--links` | 1 or more space-separated URLs | List of URLs to test. URLs should be separated by spaces. |
| `-n`, `--num-processes` | Integer | Number of threads to run in parallel when generating HTML files from Markdown. Each link is still tested serially, however. |
| `-k`, `--keep` | *None* | Option to keep temporary HTML files instead of deleting them. Only useful for debugging. |
| `-v`, `--verbose` | *None* | Increase verbosity to print all files and links tested, instead of only errors. |
