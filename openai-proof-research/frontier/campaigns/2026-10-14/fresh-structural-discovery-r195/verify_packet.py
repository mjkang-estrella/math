#!/usr/bin/env python3
"""Read-only artifact verification. Explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
from pathlib import Path

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(root, final_sha, manifest_sha, report_sha):
    for name, expected in [('FINAL.md', final_sha), ('MANIFEST.json', manifest_sha), ('REPORT.md', report_sha)]:
        if digest(root / name) != expected:
            raise ValueError('Detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    expected_paths = set()
    for row in manifest['files']:
        rel = Path(row['path'])
        if rel.is_absolute() or '..' in rel.parts or rel.as_posix() in expected_paths:
            raise ValueError('Invalid or duplicate manifest path')
        expected_paths.add(rel.as_posix())
        path = root / rel
        if path.is_symlink() or not path.is_file():
            raise ValueError('Nonregular or missing selected file: ' + str(rel))
        if path.stat().st_size != row['bytes'] or digest(path) != row['sha256']:
            raise ValueError('Selected file mismatch: ' + str(rel))
    exclusions = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
    actual = set()
    for path in root.rglob('*'):
        rel = path.relative_to(root)
        if rel.parts[0] == 'private-controls':
            continue
        if path.is_symlink():
            raise ValueError('Symlink in packet')
        if path.is_file() and rel.as_posix() not in exclusions:
            actual.add(rel.as_posix())
    if actual != expected_paths:
        raise ValueError('Selection mismatch: extra=%r missing=%r' % (sorted(actual-expected_paths), sorted(expected_paths-actual)))
    return len(expected_paths)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--final-sha', required=True)
    parser.add_argument('--manifest-sha', required=True)
    parser.add_argument('--report-sha', required=True)
    args = parser.parse_args()
    count = verify(args.root.resolve(), args.final_sha, args.manifest_sha, args.report_sha)
    print('Artifact bytes and exact selection verified:', count, 'files. No mathematical verdict.')
