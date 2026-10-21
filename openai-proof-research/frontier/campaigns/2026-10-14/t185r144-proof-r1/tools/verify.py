#!/usr/bin/env python3
"""Read-only exact-packet verifier. Three externally retained hashes are required.
This authenticates bytes and membership only, never mathematical correctness.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

OUTER = {'MANIFEST.json', 'FINAL.md', 'REPORT.md', 'ANCHORS.sha256'}
SCHEMA = 't185r144-proof-r1-exact-v1'
EXCLUDED = re.compile(r'arithmetic.*r10[789]|analytic.*r13[5678]|h138-|structural.*r14[34]|t177c143-|t373e135-|k369r134-|t088p133-|t185r144-', re.I)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe_name(value):
    if not isinstance(value, str) or not value:
        raise ValueError('invalid path')
    path = Path(value)
    if path.is_absolute() or '..' in path.parts or path.as_posix() != value:
        raise ValueError('unsafe path: ' + value)
    if any(EXCLUDED.search(part) for part in path.parts):
        raise ValueError('excluded path component: ' + value)
    return value

def inventory(root):
    files = {}
    directories = set()
    def descend(directory):
        for item in sorted(directory.iterdir()):
            rel = item.relative_to(root).as_posix()
            safe_name(rel)
            if item.is_symlink():
                raise ValueError('symlink: ' + rel)
            if item.is_dir():
                directories.add(rel)
                descend(item)
            elif item.is_file():
                data = item.read_bytes()
                files[rel] = {'bytes': len(data), 'sha256': sha(data)}
            else:
                raise ValueError('non-regular path: ' + rel)
    descend(root)
    return files, directories

def verify(root, anchors):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    for name, expected in anchors.items():
        if re.fullmatch(r'[0-9a-f]{64}', expected) is None:
            raise ValueError('malformed external anchor')
        path = root / name
        if path.is_symlink() or not path.is_file() or sha(path.read_bytes()) != expected:
            raise ValueError('external anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('schema') != SCHEMA or set(manifest.get('outer_files', [])) != OUTER:
        raise ValueError('unexpected manifest format')
    expected_files = {}
    for record in manifest['files']:
        name = safe_name(record['path'])
        if name in OUTER or name in expected_files:
            raise ValueError('duplicate or outer payload path')
        expected_files[name] = {'bytes': record['bytes'], 'sha256': record['sha256']}
    expected_directories = [safe_name(s) for s in manifest['directories']]
    if len(expected_directories) != len(set(expected_directories)):
        raise ValueError('duplicate directory')
    actual_files, actual_directories = inventory(root)
    if set(actual_files) != set(expected_files) | OUTER:
        raise ValueError('file membership mismatch')
    if actual_directories != set(expected_directories):
        raise ValueError('directory membership mismatch')
    for name, record in expected_files.items():
        if actual_files[name] != record:
            raise ValueError('payload mismatch: ' + name)
    detached = ''.join(anchors[name] + '  ' + name + '\n' for name in ['MANIFEST.json', 'FINAL.md', 'REPORT.md'])
    if (root / 'ANCHORS.sha256').read_text() != detached:
        raise ValueError('detached record mismatch')
    return len(expected_files), len(expected_directories)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    anchors = {'MANIFEST.json': args.manifest_sha256, 'FINAL.md': args.final_sha256, 'REPORT.md': args.report_sha256}
    count, directory_count = verify(args.root, anchors)
    print(json.dumps({'packet_bytes_verified': True, 'payload_files': count, 'directories': directory_count, 'mathematical_gate': False}))

if __name__ == '__main__':
    main()
