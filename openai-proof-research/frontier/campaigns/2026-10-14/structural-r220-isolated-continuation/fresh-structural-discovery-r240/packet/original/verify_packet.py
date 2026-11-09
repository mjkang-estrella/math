#!/usr/bin/env python3
"""Read-only exact-tree verifier. All three detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def safe_relative(value):
    p = PurePosixPath(value)
    require(bool(value) and not p.is_absolute() and '..' not in p.parts
            and '.' not in p.parts and p.as_posix() == value,
            'unsafe relative path')
    return value


def anchored_file(path, anchor, label):
    require(re.fullmatch('[0-9a-f]{64}', anchor) is not None, label + ': invalid anchor')
    require(not path.is_symlink() and path.is_file(), label + ': not a regular file')
    data = path.read_bytes()
    require(sha(data) == anchor, label + ': detached SHA256 mismatch')
    return data


def verify(args):
    root = Path(args.packet)
    require(not root.is_symlink() and root.is_dir(), 'packet: not a directory')
    mdata = anchored_file(Path(args.manifest), args.manifest_sha256, 'MANIFEST')
    anchored_file(Path(args.report), args.report_sha256, 'REPORT')
    final_rel = safe_relative(args.final_relative)
    anchored_file(root / final_rel, args.final_sha256, 'FINAL')
    manifest = json.loads(mdata)
    require(manifest.get('format') == 'source365-exact-tree-v1', 'manifest format')
    files = manifest['files']
    directories = manifest['directories']
    require(len({x['path'] for x in files}) == len(files), 'duplicate file path')
    require(len({x['path'] for x in directories}) == len(directories), 'duplicate directory path')
    expected_files = {safe_relative(x['path']): x for x in files}
    expected_dirs = {}
    for x in directories:
        key = x['path']
        require(key == '.' or safe_relative(key) == key, 'unsafe directory')
        expected_dirs[key] = x
    require(final_rel in expected_files, 'FINAL outside exact selection')
    require('.' in expected_dirs, 'missing root directory mode')
    actual_files = {}
    actual_dirs = {'.': root}
    stack = [root]
    while stack:
        current = stack.pop()
        with os.scandir(current) as entries:
            for entry in entries:
                p = Path(entry.path)
                rel = p.relative_to(root).as_posix()
                require(not entry.is_symlink(), 'symlink in packet: ' + rel)
                if entry.is_dir(follow_symlinks=False):
                    actual_dirs[rel] = p
                    stack.append(p)
                elif entry.is_file(follow_symlinks=False):
                    actual_files[rel] = p
                else:
                    raise ValueError('nonregular entry: ' + rel)
    require(set(actual_files) == set(expected_files), 'exact file selection mismatch')
    require(set(actual_dirs) == set(expected_dirs), 'exact directory selection mismatch')
    for rel, p in actual_dirs.items():
        mode = stat.S_IMODE(p.stat().st_mode)
        require(mode == expected_dirs[rel]['mode'], 'directory mode mismatch: ' + rel)
        require(mode & 0o222 == 0, 'writable selected directory: ' + rel)
    for rel, p in actual_files.items():
        record = expected_files[rel]
        mode = stat.S_IMODE(p.stat().st_mode)
        require(mode == record['mode'], 'file mode mismatch: ' + rel)
        require(mode & 0o222 == 0, 'writable selected file: ' + rel)
        data = p.read_bytes()
        require(len(data) == record['bytes'], 'file size mismatch: ' + rel)
        require(sha(data) == record['sha256'], 'file SHA256 mismatch: ' + rel)
    return {'verified': True, 'files': len(files), 'directories': len(directories),
            'scope': 'artifact exact selection, bytes and modes only; no mathematical grade'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['packet', 'manifest', 'final-relative', 'report',
                 'final-sha256', 'manifest-sha256', 'report-sha256']:
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args), sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print(json.dumps({'verified': False, 'error': str(exc)}))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
