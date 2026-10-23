#!/usr/bin/env python3
"""Read-only exact-packet verification against three EXPLICIT detached anchors.
This checks bytes and membership, not mathematics or rights to redistribute.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('packet', 'manifest', 'final', 'report'):
        p.add_argument('--' + name, required=True, type=Path)
    for name in ('manifest', 'final', 'report'):
        p.add_argument('--' + name + '-sha256', required=True)
    a = p.parse_args()
    for name in ('manifest', 'final', 'report'):
        path = getattr(a, name)
        expected = getattr(a, name + '_sha256')
        if path.is_symlink() or digest(path) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    m = json.loads(a.manifest.read_text(encoding='utf-8'))
    if m.get('schema') != 'r162s-exact-packet-v1':
        raise ValueError('unsupported manifest schema')
    if m['verifier_sha256'] != digest(Path(__file__)):
        raise ValueError('verifier differs from anchored manifest')
    if a.packet.is_symlink() or not a.packet.is_dir():
        raise ValueError('packet must be a real directory')
    expected = {}
    for row in m['entries']:
        rel = PurePosixPath(row['path'])
        if rel.is_absolute() or '..' in rel.parts or str(rel) != row['path'] or row['path'] in expected:
            raise ValueError('invalid or duplicate manifest path')
        expected[row['path']] = row
    actual = set()
    actual_dirs = set()
    for base, dirs, files in os.walk(a.packet, followlinks=False):
        actual_dirs.update((Path(base) / name).relative_to(a.packet).as_posix() for name in dirs)
        for name in dirs + files:
            if (Path(base) / name).is_symlink():
                raise ValueError('symlink in packet')
        for name in files:
            path = Path(base) / name
            rel = path.relative_to(a.packet).as_posix()
            actual.add(rel)
            row = expected.get(rel)
            if row is None or path.stat().st_size != row['bytes'] or digest(path) != row['sha256']:
                raise ValueError('payload mismatch: ' + rel)
    if actual_dirs != set(m['directories']):
        raise ValueError('exact packet directory membership mismatch')
    if actual != set(expected):
        raise ValueError('exact packet membership mismatch')
    print(json.dumps({'artifact_identity': 'matches explicit anchors',
                      'files': len(actual), 'mathematical_gate': False}))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as e:
        raise SystemExit(str(e))
