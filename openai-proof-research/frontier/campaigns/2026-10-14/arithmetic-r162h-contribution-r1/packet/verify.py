#!/usr/bin/env python3
"""Read-only exact-packet verification. All detached anchors are caller supplied."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(root, final_sha256, manifest_sha256, report_sha256):
    root = Path(root).resolve()
    for rel, expected in [('packet/FINAL.md', final_sha256),
                          ('MANIFEST.json', manifest_sha256),
                          ('REPORT.md', report_sha256)]:
        path = root / rel
        if path.is_symlink() or not path.is_file() or sha(path) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('schema') != 1 or manifest.get('selection') != 'packet/':
        raise ValueError('unsupported manifest schema or selection')
    expected = {}
    for row in manifest['files']:
        rel = row['path']
        path = Path(rel)
        if path.is_absolute() or '..' in path.parts or path.as_posix() != rel:
            raise ValueError('unsafe member path')
        if rel in expected:
            raise ValueError('duplicate member')
        expected[rel] = row
    packet = root / 'packet'
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError('packet is not a plain directory')
    actual = set()
    for directory, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            if (Path(directory) / name).is_symlink():
                raise ValueError('symlink in selection')
        for name in files:
            path = Path(directory) / name
            if not path.is_file():
                raise ValueError('nonregular selected member')
            actual.add(path.relative_to(packet).as_posix())
    if actual != set(expected):
        raise ValueError('exact packet membership mismatch')
    for rel, row in expected.items():
        path = packet / rel
        st = path.stat()
        if st.st_size != row['bytes'] or stat.S_IMODE(st.st_mode) != row['mode'] or sha(path) != row['sha256']:
            raise ValueError('member integrity mismatch: ' + rel)
    return len(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        count = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('ARTIFACT REJECTED: ' + str(exc))
        return 1
    print('ARTIFACT VERIFIED: %d exact members; three explicit detached anchors; no mathematical gate' % count)
    return 0


if __name__ == '__main__':
    sys.exit(main())
