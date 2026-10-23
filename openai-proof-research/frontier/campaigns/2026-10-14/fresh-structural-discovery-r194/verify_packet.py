#!/usr/bin/env python3
"""Read-only artifact verifier. Explicit detached hashes are required; no proof check."""
import argparse
import hashlib
import json
import re
from pathlib import Path, PurePosixPath

OUTSIDE = ['MANIFEST.json', 'REPORT.md', 'ANCHORS.json', 'private/controls/']

def sha(data):
    return hashlib.sha256(data).hexdigest()

def outside(path):
    return path in OUTSIDE[:3] or path.startswith(OUTSIDE[3])

def verify(root, anchors):
    root = Path(root).resolve(strict=True)
    if not root.is_dir():
        raise ValueError('root is not a directory')
    for name, expected in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('invalid detached anchor: ' + name)
        p = root / name
        if p.is_symlink() or sha(p.read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    m = json.loads((root / 'MANIFEST.json').read_bytes())
    if m.get('format') != 'r194-selected-packet-v1' or m.get('outside_manifest') != OUTSIDE:
        raise ValueError('unsupported manifest contract')
    seen = set()
    for row in m['files']:
        path = row['path']
        q = PurePosixPath(path)
        if q.is_absolute() or '..' in q.parts or q.as_posix() != path or outside(path) or path in seen:
            raise ValueError('invalid or duplicate selected path: ' + path)
        p = root / path
        if any(parent.is_symlink() for parent in [p, *p.parents] if parent != root and root in [parent, *parent.parents]):
            raise ValueError('symlink in selected path: ' + path)
        if not p.is_file() or not p.resolve().is_relative_to(root):
            raise ValueError('selected file absent/outside root: ' + path)
        b = p.read_bytes()
        if len(b) != row['bytes'] or sha(b) != row['sha256']:
            raise ValueError('selected content mismatch: ' + path)
        seen.add(path)
    if 'FINAL.md' not in seen:
        raise ValueError('FINAL.md is not selected')
    actual = set()
    for p in root.rglob('*'):
        rel = p.relative_to(root).as_posix()
        if outside(rel):
            continue
        if p.is_symlink():
            raise ValueError('unlisted symlink: ' + rel)
        if p.is_file():
            actual.add(rel)
    if actual != seen:
        raise ValueError('selection mismatch: ' + repr(sorted(actual.symmetric_difference(seen))))
    return {'artifact_integrity': 'verified', 'selected_files': len(seen), 'mathematical_gate': False}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    a = parser.parse_args()
    try:
        print(json.dumps(verify(a.root, {'FINAL.md': a.final_sha256, 'MANIFEST.json': a.manifest_sha256, 'REPORT.md': a.report_sha256}), sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError) as e:
        parser.exit(1, str(e) + '\n')
