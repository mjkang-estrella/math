#!/usr/bin/env python3
"""Read-only exact-inventory verifier for the T212M manuscript review r1 seal; MIT.
Adapted from ../t212m-formal-review-r1/verify.py and ../t212m-manuscript-v1/verify.py.
Identity only: it certifies bytes, not the mathematics or the review verdict."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

MANIFEST = 'manifest.json'
MANUSCRIPT_ANCHOR = 'c71b20126326de8eab4d016b92cca78c9e43440653361899a8335fc2747c7b3f'
VERDICT = 'PASS_FULL_MANUSCRIPT_T212M'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def inventory(root):
    files, directories = {}, []
    for base, ds, fs in os.walk(root, followlinks=False):
        for name in ds + fs:
            p = Path(base) / name
            mode = p.lstat()
            rel = p.relative_to(root).as_posix()
            require(not stat.S_ISLNK(mode.st_mode), 'symlink entry')
            if stat.S_ISDIR(mode.st_mode):
                directories.append(rel)
                continue
            require(stat.S_ISREG(mode.st_mode), 'nonregular entry')
            require(mode.st_nlink == 1, 'hardlink entry')
            if rel != MANIFEST:
                data = p.read_bytes()
                files[rel] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    return files, sorted(directories)


def verify(root, anchor):
    require(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'malformed anchor')
    require(all(not x.is_symlink() for x in (root, *root.parents)), 'symlink root ancestry')
    manifest = root / MANIFEST
    mode = manifest.lstat()
    require(stat.S_ISREG(mode.st_mode) and mode.st_nlink == 1, 'unsafe manifest')
    raw = manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == anchor, 'external anchor mismatch')
    sealed = json.loads(raw)
    require(sealed.get('verdict') == VERDICT and sealed.get('manuscript_anchor') == MANUSCRIPT_ANCHOR
            and sealed.get('acceptance_or_count_change') is False, 'manifest metadata mismatch')
    files, directories = inventory(root)
    require(files == sealed.get('files'), 'file inventory mismatch')
    require(directories == sealed.get('directories'), 'directory inventory mismatch')
    return {'status': 'PASS_IDENTITY_ONLY', 'payloads': len(files), 'directories': len(directories),
            'note': 'sealed review bytes only; not a mathematical verdict'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).absolute().parent)
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.root.absolute(), args.anchor), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        print('REJECT: ' + str(error), file=sys.stderr)
        sys.exit(1)
