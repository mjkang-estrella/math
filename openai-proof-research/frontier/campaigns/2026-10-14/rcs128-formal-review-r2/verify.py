#!/usr/bin/env python3
"""Read-only exact-membership verifier for the RCS128 formal review r2 packet.

MIT license, Myeongjin Kang (review packet). Usage: python3 -I verify.py --anchor <SHA256>.
The external anchor (SHA256 of manifest.json) is required and checked against the
raw manifest bytes BEFORE parsing. Rejects a symlinked root or ancestor, symlinks,
nonregular files, hard links, and extra or missing files or directories. Checks
bytes only; it gives no mathematical verdict. Nothing is written.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys


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
            require(not stat.S_ISLNK(mode.st_mode), 'symlink: ' + rel)
            if stat.S_ISDIR(mode.st_mode):
                directories.append(rel)
            else:
                require(stat.S_ISREG(mode.st_mode), 'nonregular: ' + rel)
                require(mode.st_nlink == 1, 'hard link: ' + rel)
                if rel != 'manifest.json':
                    data = p.read_bytes()
                    files[rel] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    return {'directories': sorted(directories), 'files': dict(sorted(files.items()))}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    require(len(args.anchor) == 64 and all(c in '0123456789abcdef' for c in args.anchor),
            'bad anchor format')
    root = Path(__file__).absolute().parent
    require(all(not x.is_symlink() for x in [root] + list(root.parents)),
            'symlink root or ancestor')
    manifest = root / 'manifest.json'
    mode = manifest.lstat()
    require(stat.S_ISREG(mode.st_mode) and mode.st_nlink == 1, 'unsafe manifest')
    raw = manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == args.anchor, 'external anchor mismatch')
    expected = json.loads(raw)
    actual = inventory(root)
    require(actual['directories'] == expected.get('directories'), 'directory membership mismatch')
    missing = sorted(set(expected.get('files', {})) - set(actual['files']))
    extra = sorted(set(actual['files']) - set(expected.get('files', {})))
    require(not missing, 'missing files: ' + ', '.join(missing))
    require(not extra, 'extra files: ' + ', '.join(extra))
    require(actual['files'] == expected['files'], 'file content mismatch')
    require(set(expected) == {'directories', 'files'}, 'unexpected manifest keys')
    print('PASS_IDENTITY_ONLY: %d files, %d directories; no mathematical or acceptance verdict'
          % (len(actual['files']), len(actual['directories'])))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
