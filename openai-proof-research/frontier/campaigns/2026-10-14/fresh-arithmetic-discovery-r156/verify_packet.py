#!/usr/bin/env python3
"""Read-only exact-packet verification. Mandatory detached anchors; no self-grading."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

EXTERIOR = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.sha256'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(root, manifest_sha, final_sha, report_sha):
    root = Path(root).resolve(strict=True)
    for name, expected in [('MANIFEST.json', manifest_sha), ('FINAL.md', final_sha), ('REPORT.md', report_sha)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit anchor for ' + name)
        p = root / name
        if p.is_symlink() or not p.is_file() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    if manifest.get('format') != 'r156-exact-packet-v1':
        raise ValueError('unrecognized manifest format')
    expected_paths = set()
    for row in manifest['files']:
        rel = row['path']
        p = Path(rel)
        if p.is_absolute() or '..' in p.parts or p.as_posix() != rel or rel in EXTERIOR or rel in expected_paths:
            raise ValueError('unsafe or duplicate path: ' + rel)
        expected_paths.add(rel)
        q = root / p
        if q.is_symlink() or not q.is_file():
            raise ValueError('missing/nonregular selected file: ' + rel)
        if q.stat().st_size != row['bytes'] or digest(q) != row['sha256']:
            raise ValueError('selected file mismatch: ' + rel)
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in packet: ' + p.relative_to(root).as_posix())
        if p.is_file():
            rel = p.relative_to(root).as_posix()
            if rel not in EXTERIOR:
                actual.add(rel)
    if actual != expected_paths:
        raise ValueError('exact file-set mismatch')
    return len(expected_paths)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    args = ap.parse_args()
    try:
        count = verify(args.root, args.manifest_sha, args.final_sha, args.report_sha)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('ARTIFACT REJECTED:', exc)
        sys.exit(1)
    print('ARTIFACT CONSISTENT:', count, 'selected files; no mathematical verdict')
