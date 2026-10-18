#!/usr/bin/env python3
"""Exact-inventory verifier for the T205M formal review r1 seal; MIT.
Identity only: it certifies bytes, not the mathematics or the review verdict."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

MANIFEST = 'review-manifest.json'
PACKET_ANCHOR = '3037eddfa1f64be85b646090df0f49484b84ff625eb0970074af86c3948ce2f2'


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
    return files, sorted(directories)


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
    require(sealed.get('verdict') == 'PASS_SCOPED_T205M' and sealed.get('packet_anchor') == PACKET_ANCHOR
            and sealed.get('full_theorem_formalized') is False, 'manifest metadata mismatch')
    files, directories = inventory(root)
    require(files == sealed['files'] and directories == sealed['directories'], 'exact inventory mismatch')
    print('PASS_IDENTITY_ONLY; sealed scoped formal review, not a full-theorem verdict')


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
