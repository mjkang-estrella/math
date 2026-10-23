#!/usr/bin/env python3
"""Read-only exact packet check. All detached anchors must be supplied explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def members(root):
    found = set()
    directories = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            p = Path(base) / name
            if p.is_symlink():
                raise ValueError('symlink forbidden')
        for name in dirs:
            directories.add((Path(base) / name).relative_to(root).as_posix())
        for name in files:
            found.add((Path(base) / name).relative_to(root).as_posix())
    return found, directories

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', required=True, type=Path)
    p.add_argument('--report', required=True, type=Path)
    for name in ('final', 'manifest', 'report'):
        p.add_argument('--' + name + '-sha256', required=True)
    a = p.parse_args()
    root = a.packet
    if root.is_symlink() or not root.is_dir() or a.report.is_symlink():
        raise ValueError('invalid anchored root/report')
    actual_files, actual_dirs = members(root)
    for path, expected in ((root / 'FINAL.md', a.final_sha256),
                           (root / 'MANIFEST.json', a.manifest_sha256),
                           (a.report, a.report_sha256)):
        if len(expected) != 64 or sha(path) != expected.lower():
            raise ValueError('detached anchor mismatch')
    data = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    expected = {}
    for item in data['files']:
        name = item['path']
        rel = PurePosixPath(name)
        if (rel.is_absolute() or '..' in rel.parts or rel.as_posix() != name
                or name in ('', '.', 'MANIFEST.json') or name in expected):
            raise ValueError('invalid manifest member')
        expected[name] = item
    if (actual_files != set(expected) | {'MANIFEST.json'}
            or actual_dirs != set(data['directories'])):
        raise ValueError('exact membership mismatch')
    for name, item in expected.items():
        path = root / name
        if path.stat().st_size != item['bytes'] or sha(path) != item['sha256']:
            raise ValueError('member content mismatch')
    print(json.dumps({'artifact_check': 'matched', 'members': len(expected),
                      'mathematical_gate': False}))

if __name__ == '__main__':
    main()
