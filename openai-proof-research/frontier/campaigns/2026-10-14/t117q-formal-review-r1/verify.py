#!/usr/bin/env python3
"""Read-only exact membership verification of t117q-formal-review-r1 (MIT).

Identity only: it authenticates review-manifest.json by an external SHA256 anchor and requires the
directory's exact file/directory membership and file hashes to match it. No mathematical verdict.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

MANIFEST = 'review-manifest.json'


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
            require(not stat.S_ISLNK(mode.st_mode), 'symlink')
            if stat.S_ISDIR(mode.st_mode):
                directories.append(rel)
            else:
                require(stat.S_ISREG(mode.st_mode) and mode.st_nlink == 1, 'nonregular or hardlink')
                if rel != MANIFEST:
                    data = p.read_bytes()
                    files[rel] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    return {'files': dict(sorted(files.items())), 'directories': sorted(directories)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    require(len(args.anchor) == 64 and all(c in '0123456789abcdef' for c in args.anchor), 'bad anchor')
    root = Path(__file__).absolute().parent
    require(all(not x.is_symlink() for x in [root] + list(root.parents)), 'symlink root or ancestor')
    manifest = root / MANIFEST
    mode = manifest.lstat()
    require(stat.S_ISREG(mode.st_mode) and mode.st_nlink == 1, 'unsafe manifest')
    raw = manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == args.anchor, 'external anchor mismatch')
    sealed = json.loads(raw)
    require(inventory(root) == {'files': sealed['files'], 'directories': sealed['directories']},
            'exact membership mismatch')
    print('PASS_REVIEW_IDENTITY_ONLY; verdict text is in review.md')


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
