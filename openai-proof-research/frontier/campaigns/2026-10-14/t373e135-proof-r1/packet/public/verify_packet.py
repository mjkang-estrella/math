#!/usr/bin/env python3
"""Read-only exact-byte verifier; independent detached anchors are required.

This verifies no mathematics, historical originals, modes, empty directories,
hard-link provenance, or operating-system write isolation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat


def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def regular(p):
    if not stat.S_ISREG(p.lstat().st_mode):
        raise ValueError('not a nonsymlink regular file: ' + str(p))


def verify(root, manifest_sha, final_sha, report_sha):
    if root.is_symlink() or (root / 'packet').is_symlink():
        raise ValueError('symlink root or packet')
    for rel, anchor in [('packet/MANIFEST.json', manifest_sha),
                        ('FINAL.md', final_sha), ('REPORT.md', report_sha)]:
        if not re.fullmatch('[0-9a-f]{64}', anchor):
            raise ValueError('invalid detached anchor')
        p = root / rel
        regular(p)
        if digest(p) != anchor:
            raise ValueError('detached anchor mismatch: ' + rel)
    obj = json.loads((root / 'packet/MANIFEST.json').read_text())
    if obj.get('schema') != 't373e135-proof-r1-exact-v1':
        raise ValueError('wrong schema')
    expected = {}
    for row in obj['files']:
        name = row['path']
        p = Path(name)
        if p.is_absolute() or str(p) != name or '..' in p.parts or name in ('', '.', 'MANIFEST.json'):
            raise ValueError('unsafe manifest path')
        if name in expected or not isinstance(row['size'], int) or row['size'] < 0:
            raise ValueError('duplicate path or invalid size')
        if not re.fullmatch('[0-9a-f]{64}', row['sha256']):
            raise ValueError('invalid file digest')
        expected[name] = row
    actual = set()
    for cur, dirs, files in os.walk(root / 'packet', followlinks=False):
        for name in dirs:
            if not stat.S_ISDIR((Path(cur) / name).lstat().st_mode):
                raise ValueError('symlink or special directory')
        for name in files:
            p = Path(cur) / name
            regular(p)
            actual.add(p.relative_to(root / 'packet').as_posix())
    if actual != set(expected) | {'MANIFEST.json'}:
        raise ValueError('exact regular-file membership mismatch')
    total = 0
    for name, row in expected.items():
        p = root / 'packet' / name
        if p.stat().st_size != row['size'] or digest(p) != row['sha256']:
            raise ValueError('file bytes mismatch: ' + name)
        total += row['size']
    final = (root / 'FINAL.md').read_text()
    for value in [manifest_sha, report_sha, digest(root / 'packet/public/verify_packet.py')]:
        if value not in final:
            raise ValueError('FINAL binding missing')
    for name, value in [
        ('FROZEN-SCOPE.md', 'cc80f307514d0fe7ab47079b6cda7d47abb7ce4c80aa616d0ebc02cc1b96e939'),
        ('author-proof.md', 'b3159d956644b4fd5befcf55de5a965eb91278798f6b8f57f713a84aab0d2172')]:
        p = root / 'packet/private/incoming/packet/public' / name
        if digest(p) != value or value not in final:
            raise ValueError('unchanged incoming byte binding missing')
    return {'integrity': 'verified', 'files_excluding_manifest': len(expected),
            'bytes_excluding_manifest': total,
            'anchors': {'manifest': manifest_sha, 'final': final_sha, 'report': report_sha},
            'limits': 'Exact regular-file bytes only; no mathematical or historical-preservation conclusion.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root', type=Path)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    a = ap.parse_args()
    try:
        print(json.dumps(verify(a.root, a.manifest_sha, a.final_sha, a.report_sha), indent=2))
        return 0
    except Exception as e:
        print(json.dumps({'integrity': 'rejected', 'reason': str(e)}))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
