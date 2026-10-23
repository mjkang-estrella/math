#!/usr/bin/env python3
"""Read-only artifact verification. No mathematical verdict is produced."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    for name, expected in [('packet/FINAL.md', final_sha),
                           ('MANIFEST.json', manifest_sha),
                           ('REPORT.md', report_sha)]:
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or symlink anchor: ' + name)
        if len(expected) != 64 or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('schema') != 'arithmetic162j-exact-packet-v1':
        raise ValueError('unknown manifest schema')
    entries = manifest['files']
    expected_paths = set()
    for entry in entries:
        name = entry['path']
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or not name.startswith('packet/'):
            raise ValueError('unsafe manifest path')
        if name in expected_paths:
            raise ValueError('duplicate manifest path')
        expected_paths.add(name)
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or symlink payload: ' + name)
        if p.stat().st_size != entry['bytes'] or digest(p) != entry['sha256']:
            raise ValueError('payload mismatch: ' + name)
    actual = set()
    for directory, dirs, files in os.walk(root / 'packet', followlinks=False):
        for name in dirs + files:
            if (Path(directory) / name).is_symlink():
                raise ValueError('payload contains a symlink')
        for name in files:
            actual.add((Path(directory) / name).relative_to(root).as_posix())
    if actual != expected_paths:
        raise ValueError('payload set mismatch: missing=' + repr(sorted(expected_paths-actual))
                         + ' extra=' + repr(sorted(actual-expected_paths)))
    return len(entries)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        count = verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256)
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as e:
        print('ARTIFACT CHECK FAILED:', str(e), file=sys.stderr)
        return 1
    print('ARTIFACT CHECK MATCHED:', count, 'payload files and 3 explicit detached anchors; no mathematical gate')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
