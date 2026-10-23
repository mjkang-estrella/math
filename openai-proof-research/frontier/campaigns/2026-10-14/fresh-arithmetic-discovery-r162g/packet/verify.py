#!/usr/bin/env python3
"""Read-only verification of one explicitly anchored research packet."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    for name in ('final', 'manifest', 'report'):
        ap.add_argument('--' + name + '-sha256', required=True)
    args = ap.parse_args()
    root = Path(args.root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    expected_anchors = {
        'packet/FINAL.md': args.final_sha256,
        'MANIFEST.json': args.manifest_sha256,
        'REPORT.md': args.report_sha256,
    }
    for rel, expected in expected_anchors.items():
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit SHA256 anchor')
        path = root / rel
        if path.is_symlink() or not path.is_file() or digest(path) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    packet = root / 'packet'
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError('packet must be a real directory')
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('format') != 'exact-packet-v1':
        raise ValueError('unsupported manifest format')
    expected = {}
    for entry in manifest['files']:
        rel = entry['path']
        parts = PurePosixPath(rel).parts
        if (not isinstance(rel, str) or PurePosixPath(rel).is_absolute()
                or '..' in parts or not parts or parts[0] != 'packet'
                or PurePosixPath(rel).as_posix() != rel or rel in expected):
            raise ValueError('invalid or duplicate manifest path')
        expected[rel] = entry
    actual = {}
    for path in packet.rglob('*'):
        if path.is_symlink():
            raise ValueError('symlink in packet')
        if path.is_file():
            actual[path.relative_to(root).as_posix()] = path
        elif not path.is_dir():
            raise ValueError('special file in packet')
    if set(actual) != set(expected):
        raise ValueError('packet membership mismatch')
    for rel, path in actual.items():
        entry = expected[rel]
        if path.stat().st_size != entry['size'] or digest(path) != entry['sha256']:
            raise ValueError('file content mismatch: ' + rel)
    return {'artifact_bytes_and_membership_match': True, 'file_count': len(actual),
            'mathematical_review': 'not performed by this verifier'}


if __name__ == '__main__':
    try:
        print(json.dumps(main(), sort_keys=True))
    except Exception as exc:
        print(json.dumps({'artifact_bytes_and_membership_match': False,
                          'error': str(exc)}, sort_keys=True))
        sys.exit(1)
