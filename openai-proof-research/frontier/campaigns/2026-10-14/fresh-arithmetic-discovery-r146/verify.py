#!/usr/bin/env python3
"""Read-only exact-file packet check. Explicit anchors are mandatory; no self-trust."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

ENVELOPES = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}

def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def verify(root, anchors):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('invalid packet root')
    for name in ['FINAL.md', 'MANIFEST.json', 'REPORT.md']:
        p = root / name
        if p.is_symlink() or not p.is_file() or digest(p) != anchors[name]:
            raise ValueError('detached anchor mismatch: ' + name)
    if json.loads((root / 'ANCHORS.json').read_text()) != anchors:
        raise ValueError('anchor record differs from supplied anchors')
    data = json.loads((root / 'MANIFEST.json').read_text())
    if data['excluded_envelopes'] != sorted(ENVELOPES):
        raise ValueError('unexpected envelope exclusions')
    expected = {}
    for rec in data['files']:
        name = rec['path']
        parts = PurePosixPath(name)
        if (parts.is_absolute() or '..' in parts.parts or str(parts) != name
                or '\\' in name or name in expected or name in ENVELOPES):
            raise ValueError('unsafe or duplicate manifest path')
        expected[name] = rec
    actual = set()
    for parent, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            p = Path(parent) / name
            if p.is_symlink():
                raise ValueError('symlink in packet')
        for name in names:
            p = Path(parent) / name
            if not p.is_file():
                raise ValueError('nonregular file')
            actual.add(p.relative_to(root).as_posix())
    if actual != set(expected) | ENVELOPES:
        raise ValueError('exact file membership mismatch')
    for name, rec in expected.items():
        p = root / name
        if p.stat().st_size != rec['bytes'] or digest(p) != rec['sha256']:
            raise ValueError('payload mismatch: ' + name)
    return len(expected)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    anchors = {'FINAL.md': args.final_sha256, 'MANIFEST.json': args.manifest_sha256,
               'REPORT.md': args.report_sha256}
    try:
        n = verify(args.root, anchors)
    except (ValueError, KeyError, OSError, TypeError) as e:
        parser.exit(1, 'ARTIFACT CHECK FAILED: ' + str(e) + '\n')
    print('ARTIFACT CHECK OK: ' + str(n) + ' payload files; exact membership and supplied anchors. No mathematical gate.')
