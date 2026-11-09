#!/usr/bin/env python3
"""Read-only exact packet verification against three EXPLICIT detached SHA256s.
No automatic anchor discovery, writes, repair, upstream reads or mathematical gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
sys.dont_write_bytecode = True

def digest(data):
    return hashlib.sha256(data).hexdigest()

def checked_path(value):
    if not isinstance(value, str):
        raise ValueError('non-string member')
    p = PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or str(p) != value or not value.startswith('packet/'):
        raise ValueError('unsafe or noncanonical member')
    return value

def verify(root, expected):
    for name, want in expected.items():
        if not re.fullmatch(r'[0-9a-f]{64}', want):
            raise ValueError('invalid explicit SHA256: ' + name)
        p = root / name
        if not stat.S_ISREG(p.lstat().st_mode):
            raise ValueError('detached object is not regular: ' + name)
        if digest(p.read_bytes()) != want:
            raise ValueError('detached SHA256 mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    if manifest.get('schema') != 'r162w-independent-contribution-packet-v1':
        raise ValueError('unexpected manifest schema')
    required_files = {}
    required_dirs = {}
    for entry in manifest['files']:
        name = checked_path(entry['path'])
        if name in required_files:
            raise ValueError('duplicate file')
        required_files[name] = entry
    for entry in manifest['directories']:
        name = entry['path']
        if name != 'packet':
            checked_path(name)
        if name in required_dirs or name in required_files:
            raise ValueError('duplicate or conflicting directory')
        required_dirs[name] = entry
    packet = root / 'packet'
    if not stat.S_ISDIR(packet.lstat().st_mode):
        raise ValueError('packet is not a real directory')
    actual_files = {}
    actual_dirs = {}
    for base, dirs, files in os.walk(packet, followlinks=False):
        directory = Path(base)
        actual_dirs[directory.relative_to(root).as_posix()] = directory.lstat().st_mode
        for name in dirs:
            if not stat.S_ISDIR((directory / name).lstat().st_mode):
                raise ValueError('symlink or non-directory member')
        for name in files:
            p = directory / name
            st = p.lstat()
            if not stat.S_ISREG(st.st_mode):
                raise ValueError('symlink or non-regular member')
            actual_files[p.relative_to(root).as_posix()] = (p, st)
    if set(actual_files) != set(required_files) or set(actual_dirs) != set(required_dirs):
        raise ValueError('exact packet membership mismatch')
    for name, mode in actual_dirs.items():
        if mode != required_dirs[name]['mode']:
            raise ValueError('directory mode mismatch: ' + name)
    for name, (p, st) in actual_files.items():
        entry = required_files[name]
        if st.st_mode != entry['mode'] or st.st_size != entry['bytes']:
            raise ValueError('byte length or mode mismatch: ' + name)
        if digest(p.read_bytes()) != entry['sha256']:
            raise ValueError('member SHA256 mismatch: ' + name)
    return len(actual_files)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    try:
        n = verify(args.root, {'FINAL.md': args.final_sha256,
                              'MANIFEST.json': args.manifest_sha256,
                              'REPORT.md': args.report_sha256})
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('INTEGRITY REJECT: ' + str(exc), file=sys.stderr)
        return 1
    print('INTEGRITY OK: three explicit anchors; exact bytes, modes and membership; '
          + str(n) + ' files. No mathematical verdict is inferred.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
