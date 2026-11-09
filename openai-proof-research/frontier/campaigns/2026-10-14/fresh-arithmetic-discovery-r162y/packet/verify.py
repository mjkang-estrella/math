#!/usr/bin/env python3
"""Read-only explicit-anchor artifact verifier. This is not a mathematical gate."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def verify(root, anchors):
    fixed = {'final': 'FINAL.md', 'manifest': 'packet/private/MANIFEST.json',
             'report': 'REPORT.md'}
    for key, relative in fixed.items():
        p = root / relative
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or symlink anchor: ' + relative)
        expected = anchors[key]
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit SHA256: ' + key)
        if digest(p) != expected:
            raise ValueError('anchor mismatch: ' + key)
    manifest = json.loads((root / fixed['manifest']).read_text(encoding='utf-8'))
    if manifest.get('format') != 'r162y-exact-packet-v1':
        raise ValueError('unsupported manifest')
    packet = root / 'packet'
    excluded = 'private/MANIFEST.json'
    expected_paths = set()
    for entry in manifest['files']:
        relative = entry['path']
        posix = PurePosixPath(relative)
        if (posix.is_absolute() or '..' in posix.parts or
                posix.as_posix() != relative or relative == excluded or
                relative in expected_paths):
            raise ValueError('invalid or duplicate packet path')
        expected_paths.add(relative)
        p = packet / relative
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or symlink packet file: ' + relative)
        if p.stat().st_size != entry['bytes'] or digest(p) != entry['sha256']:
            raise ValueError('packet byte mismatch: ' + relative)
    actual = set()
    for p in packet.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in packet')
        if p.is_file():
            relative = p.relative_to(packet).as_posix()
            if relative != excluded:
                actual.add(relative)
    if actual != expected_paths:
        raise ValueError('packet membership mismatch')
    return len(expected_paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--final-sha', required=True)
    parser.add_argument('--manifest-sha', required=True)
    parser.add_argument('--report-sha', required=True)
    args = parser.parse_args()
    try:
        count = verify(args.root, {'final': args.final_sha,
                                  'manifest': args.manifest_sha,
                                  'report': args.report_sha})
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('ARTIFACT CHECK FAILED: ' + str(exc), file=sys.stderr)
        return 1
    print('ARTIFACT CHECK ONLY: verified three explicit anchors and '
          + str(count) + ' exact packet files; no mathematical gate.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
