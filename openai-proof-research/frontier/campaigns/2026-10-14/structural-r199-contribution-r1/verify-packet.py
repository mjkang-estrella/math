#!/usr/bin/env python3
"""Read-only verification of this review's exact selection; no mathematical grade.
All three SHA256 anchors must be supplied explicitly by the caller.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

SCHEMA = 'structural-r199-contribution-r1-exact-v1'
OUTSIDE = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
OMITTED = 'private/copied-controls'

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def mode(path):
    return format(stat.S_IMODE(path.lstat().st_mode), '04o')

def safe(s):
    if not isinstance(s, str) or not s:
        raise ValueError('invalid relative path')
    p = PurePosixPath(s)
    if p.is_absolute() or '..' in p.parts or '\\' in s or p.as_posix() != s:
        raise ValueError('unsafe/noncanonical relative path')
    return s

def omitted(s):
    return s == OMITTED or s.startswith(OMITTED + '/')

def verify(args):
    root = Path(args.root).resolve(strict=True)
    for v in (args.final_sha256, args.manifest_sha256, args.report_sha256):
        if re.fullmatch('[0-9a-f]{64}', v) is None:
            raise ValueError('three explicit SHA256 anchors required')
    for name, anchor in [('MANIFEST.json', args.manifest_sha256),
                         ('FINAL.md', args.final_sha256),
                         ('REPORT.md', args.report_sha256)]:
        p = root / name
        if p.is_symlink() or not stat.S_ISREG(p.lstat().st_mode) or sha(p) != anchor:
            raise ValueError(name + ' detached anchor mismatch')
    m = json.loads((root / 'MANIFEST.json').read_text())
    if m.get('schema') != SCHEMA:
        raise ValueError('schema mismatch')
    if set(m['outside_selection_files']) != OUTSIDE or m['outside_selection_prefixes'] != [OMITTED + '/']:
        raise ValueError('outside-selection policy mismatch')
    selected = {}
    for row in m['files']:
        rel = safe(row['path'])
        if rel in selected or rel in OUTSIDE or omitted(rel):
            raise ValueError('duplicate or disallowed selected path')
        selected[rel] = row
    if 'FINAL.md' not in selected or len({s.casefold() for s in selected}) != len(selected):
        raise ValueError('FINAL missing or casefold collision')
    dirs_expected = {}
    for row in m['directories']:
        rel = row['path']
        if rel != '.':
            safe(rel)
        if rel in dirs_expected or omitted(rel):
            raise ValueError('duplicate or disallowed directory')
        dirs_expected[rel] = row['mode']
    actual_files, actual_dirs = set(), {'.'}
    for current, dirs, files in os.walk(root, topdown=True, followlinks=False):
        keep = []
        for name in dirs:
            p = Path(current) / name
            rel = p.relative_to(root).as_posix()
            if omitted(rel):
                continue
            if p.is_symlink() or not stat.S_ISDIR(p.lstat().st_mode):
                raise ValueError('nonordinary directory ' + rel)
            keep.append(name)
            actual_dirs.add(rel)
        dirs[:] = keep
        for name in files:
            p = Path(current) / name
            rel = p.relative_to(root).as_posix()
            if omitted(rel):
                continue
            if p.is_symlink() or not stat.S_ISREG(p.lstat().st_mode):
                raise ValueError('nonregular file ' + rel)
            actual_files.add(rel)
    if actual_files != set(selected) | OUTSIDE:
        raise ValueError('exact file membership mismatch')
    if actual_dirs != set(dirs_expected):
        raise ValueError('exact directory membership mismatch')
    for rel, expected in dirs_expected.items():
        if mode(root / rel) != expected:
            raise ValueError('directory mode mismatch ' + rel)
    if set(m['outside_selection_modes']) != OUTSIDE:
        raise ValueError('outside modes mismatch')
    for rel, expected in m['outside_selection_modes'].items():
        if mode(root / rel) != expected:
            raise ValueError('outside file mode mismatch ' + rel)
    for rel, row in selected.items():
        p = root / rel
        if mode(p) != row['mode']:
            raise ValueError('file mode mismatch ' + rel)
        if p.stat().st_size != row['bytes']:
            raise ValueError('byte length mismatch ' + rel)
        if sha(p) != row['sha256']:
            raise ValueError('content hash mismatch ' + rel)
    return {'artifact_verification': 'OK', 'selected_files': len(selected),
            'selected_directories': len(dirs_expected),
            'selected_bytes': sum(x['bytes'] for x in selected.values()),
            'mathematical_verdict': None}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        print(json.dumps(verify(a), sort_keys=True))
    except Exception as e:
        print(json.dumps({'artifact_verification': 'REJECT', 'reason': str(e),
                          'mathematical_verdict': None}, sort_keys=True))
        sys.exit(1)
