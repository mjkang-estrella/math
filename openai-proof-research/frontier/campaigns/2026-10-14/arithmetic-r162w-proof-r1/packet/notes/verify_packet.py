#!/usr/bin/env python3
"""Read-only exact packet verifier. Explicit detached anchors are mandatory.
Integrity checks do not establish mathematical correctness.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def exact_members(root):
    packet = root / 'packet'
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError('invalid packet directory')
    found = {}
    for directory, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs:
            p = Path(directory) / name
            if p.is_symlink():
                raise ValueError('symlink directory')
        for name in files:
            p = Path(directory) / name
            st = p.lstat()
            if not stat.S_ISREG(st.st_mode):
                raise ValueError('nonregular member')
            b = p.read_bytes()
            found[p.relative_to(root).as_posix()] = {
                'bytes': len(b), 'mode': st.st_mode, 'sha256': digest(b)
            }
    return found


def check(root, anchors):
    for name, expected in anchors.items():
        if not re.fullmatch(r'[0-9a-f]{64}', expected):
            raise ValueError('invalid explicit anchor')
        p = root / name
        if not stat.S_ISREG(p.lstat().st_mode) or digest(p.read_bytes()) != expected:
            raise ValueError('anchor mismatch: ' + name)
    m = json.loads((root / 'MANIFEST.json').read_bytes())
    if m.get('schema') != 'r162w-independent-review-packet-v1':
        raise ValueError('manifest schema')
    entries = {}
    for e in m['entries']:
        name = e['path']
        path = PurePosixPath(name)
        if (path.is_absolute() or '..' in path.parts or '.' in path.parts
                or path.as_posix() != name or not name.startswith('packet/')
                or '\\' in name or name in entries):
            raise ValueError('unsafe or duplicate manifest member')
        entries[name] = {k: e[k] for k in ('bytes', 'mode', 'sha256')}
    actual = exact_members(root)
    if actual.keys() != entries.keys():
        raise ValueError('packet membership mismatch')
    for name, expected in entries.items():
        if actual[name] != expected:
            raise ValueError('member bytes/hash/mode mismatch: ' + name)
    if len(entries) != m['file_count'] or sum(e['bytes'] for e in entries.values()) != m['total_bytes']:
        raise ValueError('manifest totals mismatch')
    return len(entries)


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument('--root', required=True, type=Path)
    a.add_argument('--final-sha256', required=True)
    a.add_argument('--manifest-sha256', required=True)
    a.add_argument('--report-sha256', required=True)
    x = a.parse_args()
    try:
        count = check(x.root, {'FINAL.md': x.final_sha256,
                              'MANIFEST.json': x.manifest_sha256,
                              'REPORT.md': x.report_sha256})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print('REJECT:', error, file=sys.stderr)
        return 1
    print('VERIFIED:', count, 'exact packet files and three explicit detached anchors; integrity only')
    return 0


if __name__ == '__main__':
    sys.exit(main())
