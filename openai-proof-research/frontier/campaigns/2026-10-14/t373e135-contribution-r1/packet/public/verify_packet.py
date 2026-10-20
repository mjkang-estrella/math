#!/usr/bin/env python3
"""Read-only byte verifier; explicit detached anchors required. No mathematical gates."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def regular(path):
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError('not a regular nonsymlink file: ' + str(path))


def verify(root, final_sha, manifest_sha, report_sha):
    if root.is_symlink() or (root / 'packet').is_symlink():
        raise ValueError('root/packet symlink')
    for rel, anchor in [('FINAL.md', final_sha), ('packet/MANIFEST.json', manifest_sha),
                        ('REPORT.md', report_sha)]:
        if not re.fullmatch(r'[0-9a-f]{64}', anchor):
            raise ValueError('invalid detached anchor')
        regular(root / rel)
        if sha(root / rel) != anchor:
            raise ValueError('detached mismatch: ' + rel)
    manifest = json.loads((root / 'packet/MANIFEST.json').read_text())
    if manifest.get('schema') != 't373e135-contribution-r1-exact-files-v1':
        raise ValueError('manifest schema')
    expected = {}
    for r in manifest['files']:
        s = r['path']
        p = Path(s)
        if p.is_absolute() or p.as_posix() != s or '..' in p.parts or s in ('', '.', 'MANIFEST.json'):
            raise ValueError('unsafe manifest path')
        if s in expected or not isinstance(r['size'], int) or r['size'] < 0:
            raise ValueError('duplicate path or invalid size')
        if not re.fullmatch(r'[0-9a-f]{64}', r['sha256']):
            raise ValueError('invalid file hash')
        expected[s] = r
    actual = set()
    for cur, dirs, files in os.walk(root / 'packet', followlinks=False):
        for n in dirs:
            if not stat.S_ISDIR((Path(cur) / n).lstat().st_mode):
                raise ValueError('special/symlink directory')
        for n in files:
            p = Path(cur) / n
            regular(p)
            actual.add(p.relative_to(root / 'packet').as_posix())
    if actual != set(expected) | {'MANIFEST.json'}:
        raise ValueError('exact regular-file membership mismatch')
    for s, r in expected.items():
        p = root / 'packet' / s
        if p.stat().st_size != r['size'] or sha(p) != r['sha256']:
            raise ValueError('content mismatch: ' + s)
    final = (root / 'FINAL.md').read_text()
    for value in [manifest_sha, report_sha, sha(root / 'packet/public/verify_packet.py')]:
        if value not in final:
            raise ValueError('FINAL binding missing')
    return {'byte_integrity': 'verified', 'files_excluding_manifest': len(expected),
            'bytes_excluding_manifest': sum(r['size'] for r in expected.values()),
            'limits': 'No mathematics, modes, emptydirs, hardlinks, historical/current originals or OS confinement certified.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('root', type=Path)
    p.add_argument('--final-sha', required=True)
    p.add_argument('--manifest-sha', required=True)
    p.add_argument('--report-sha', required=True)
    a = p.parse_args()
    try:
        print(json.dumps(verify(a.root, a.final_sha, a.manifest_sha, a.report_sha), indent=2))
        return 0
    except Exception as e:
        print(json.dumps({'byte_integrity': 'rejected', 'reason': str(e)}))
        return 1


if __name__ == '__main__':
    sys.exit(main())
