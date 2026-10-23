#!/usr/bin/env python3
"""Read-only exact packet/mode verifier; artifact checks never certify mathematics.
All three SHA256 anchors must be supplied explicitly from the detached handoff.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

SCHEMA = 'structural199-proof-r1-exact-selection-v1'
OUTSIDE = {'MANIFEST.json', 'ANCHORS.json', 'REPORT.md'}
OMITTED = 'private/copied-controls'

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def mode(path):
    return format(stat.S_IMODE(path.lstat().st_mode), '04o')

def safe(value, directory=False):
    if directory and value == '.':
        return value
    if not isinstance(value, str) or not value:
        raise ValueError('invalid path')
    p = PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or '\\' in value or p.as_posix() != value or value == '.':
        raise ValueError('noncanonical path')
    return value

def omitted(rel):
    return rel == OMITTED or rel.startswith(OMITTED + '/')

def verify(args):
    root = Path(args.root)
    if root.is_symlink():
        raise ValueError('symlink root')
    root = root.resolve(strict=True)
    anchors = {'FINAL.md': args.final_sha256, 'MANIFEST.json': args.manifest_sha256, 'REPORT.md': args.report_sha256}
    for name, value in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', value):
            raise ValueError('explicit SHA256 required')
        path = root / name
        if path.is_symlink() or not path.is_file() or sha(path) != value:
            raise ValueError(name + ' detached anchor mismatch')
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest['schema'] != SCHEMA:
        raise ValueError('wrong schema')
    if set(manifest['outside_selection_files']) != OUTSIDE or manifest['outside_selection_prefixes'] != [OMITTED + '/']:
        raise ValueError('unexpected exclusion policy')
    selected = {}
    for row in manifest['files']:
        rel = safe(row['path'])
        if rel in selected or rel in OUTSIDE or omitted(rel):
            raise ValueError('duplicate/omitted selected member')
        selected[rel] = row
    if 'FINAL.md' not in selected or len({p.casefold() for p in selected}) != len(selected):
        raise ValueError('FINAL missing or casefold collision')
    directories = {}
    for row in manifest['directories']:
        rel = safe(row['path'], directory=True)
        if rel in directories or omitted(rel):
            raise ValueError('duplicate/omitted directory')
        directories[rel] = row['mode']
    if '.' not in directories:
        raise ValueError('root directory missing')
    files_found, dirs_found = set(), {'.'}
    for current, dirs, files in os.walk(root, topdown=True, followlinks=False):
        keep = []
        for name in dirs:
            path = Path(current) / name
            rel = path.relative_to(root).as_posix()
            if omitted(rel):
                continue
            if path.is_symlink() or not stat.S_ISDIR(path.lstat().st_mode):
                raise ValueError('nonordinary directory ' + rel)
            dirs_found.add(rel)
            keep.append(name)
        dirs[:] = keep
        for name in files:
            path = Path(current) / name
            rel = path.relative_to(root).as_posix()
            if omitted(rel):
                continue
            if path.is_symlink() or not stat.S_ISREG(path.lstat().st_mode):
                raise ValueError('nonordinary file ' + rel)
            files_found.add(rel)
    if files_found != set(selected) | OUTSIDE or dirs_found != set(directories):
        raise ValueError('exact membership mismatch')
    for rel, expected in directories.items():
        if mode(root / rel) != expected:
            raise ValueError('directory mode mismatch ' + rel)
    if set(manifest['outside_selection_modes']) != OUTSIDE:
        raise ValueError('outside modes missing')
    for rel, expected in manifest['outside_selection_modes'].items():
        if mode(root / rel) != expected:
            raise ValueError('outside mode mismatch ' + rel)
    for rel, row in selected.items():
        path = root / rel
        if mode(path) != row['mode']:
            raise ValueError('file mode mismatch ' + rel)
        if path.stat().st_size != row['bytes'] or sha(path) != row['sha256']:
            raise ValueError('content mismatch ' + rel)
    recorded = json.loads((root / 'ANCHORS.json').read_text())
    if recorded.get('algorithm') != 'SHA256' or any(recorded.get(k) != v for k, v in anchors.items()):
        raise ValueError('detached record mismatch')
    return {'artifact_verification': 'OK', 'selected_files': len(selected), 'selected_directories': len(directories), 'selected_bytes': sum(r['bytes'] for r in selected.values()), 'mathematical_verdict': None}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args), sort_keys=True))
    except Exception as exc:
        print(json.dumps({'artifact_verification': 'REJECT', 'reason': str(exc), 'mathematical_verdict': None}, sort_keys=True))
        sys.exit(1)
