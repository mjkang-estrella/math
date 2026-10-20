#!/usr/bin/env python3
"""Read-only byte-integrity verifier. Requires independent detached anchors.

This does not execute packet research code, change permissions, or decide any
mathematical or contribution question. It ignores file modes and empty dirs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def regular(path):
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError(f'not a regular nonsymlink file: {path}')


def verify(root, manifest_sha, final_sha, report_sha):
    if root.is_symlink() or (root / 'packet').is_symlink():
        raise ValueError('symlink root/packet is not allowed')
    for rel, anchor in [('packet/MANIFEST.json', manifest_sha),
                        ('FINAL.md', final_sha), ('REPORT.md', report_sha)]:
        if not re.fullmatch('[0-9a-f]{64}', anchor):
            raise ValueError(f'invalid detached anchor for {rel}')
        p = root / rel
        regular(p)
        if digest(p) != anchor:
            raise ValueError(f'detached anchor mismatch: {rel}')
    manifest = json.loads((root / 'packet/MANIFEST.json').read_text())
    if manifest.get('schema') != 'r135-exact-files-v1':
        raise ValueError('unexpected manifest schema')
    expected = {}
    for record in manifest['files']:
        s = record['path']
        p = Path(s)
        if p.is_absolute() or str(p) != s or '..' in p.parts or s in ('', '.', 'MANIFEST.json'):
            raise ValueError(f'unsafe/reserved manifest path: {s}')
        if s in expected:
            raise ValueError(f'duplicate manifest path: {s}')
        if not isinstance(record['size'], int) or record['size'] < 0:
            raise ValueError('invalid size')
        if not re.fullmatch('[0-9a-f]{64}', record['sha256']):
            raise ValueError('invalid content hash')
        expected[s] = record
    actual = set()
    packet = root / 'packet'
    for cur, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs:
            if not stat.S_ISDIR((Path(cur) / name).lstat().st_mode):
                raise ValueError('symlink or special directory in packet')
        for name in files:
            p = Path(cur) / name
            regular(p)
            actual.add(p.relative_to(packet).as_posix())
    if actual != set(expected) | {'MANIFEST.json'}:
        raise ValueError('exact file set mismatch: ' + json.dumps({
            'missing': sorted(set(expected) - actual),
            'extra': sorted(actual - set(expected) - {'MANIFEST.json'})}))
    total = 0
    for s, record in expected.items():
        p = packet / s
        if p.stat().st_size != record['size'] or digest(p) != record['sha256']:
            raise ValueError(f'packet content mismatch: {s}')
        total += record['size']
    return {'integrity': 'verified', 'files_excluding_manifest': len(expected),
            'bytes_excluding_manifest': total,
            'anchors': {'manifest': manifest_sha, 'final': final_sha, 'report': report_sha},
            'limits': 'byte integrity only; no mathematical, contribution or historical-preservation verdict'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root', type=Path)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    a = ap.parse_args()
    try:
        result = verify(a.root, a.manifest_sha, a.final_sha, a.report_sha)
    except Exception as e:
        print(json.dumps({'integrity': 'rejected', 'reason': str(e)}))
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    sys.exit(main())
