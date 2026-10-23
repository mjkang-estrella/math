#!/usr/bin/env python3
"""Read-only integrity verification. No mathematical gate is evaluated."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

def digest(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('expected a regular non-symlink file')
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()

def anchor(path, expected):
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('expected an explicit lowercase SHA256 anchor')
    if digest(path) != expected:
        raise ValueError('detached anchor mismatch')

def run():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest='mode', required=True)
    single = modes.add_parser('file')
    single.add_argument('--file', type=Path, required=True)
    single.add_argument('--sha256', required=True)
    packet = modes.add_parser('packet')
    packet.add_argument('--root', type=Path, required=True)
    packet.add_argument('--final-sha256', required=True)
    packet.add_argument('--manifest-sha256', required=True)
    packet.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    if args.mode == 'file':
        anchor(args.file, args.sha256)
        print('PASS: explicit file anchor matches; read-only integrity only.')
        return
    root = args.root
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a non-symlink directory')
    root = root.resolve()
    for name in ['packet', 'private']:
        if (root / name).is_symlink() or not (root / name).is_dir():
            raise ValueError('packet and private must be regular directories')
    anchor(root / 'FINAL.md', args.final_sha256)
    anchor(root / 'private/MANIFEST.json', args.manifest_sha256)
    anchor(root / 'REPORT.md', args.report_sha256)
    manifest = json.loads((root / 'private/MANIFEST.json').read_bytes())
    if manifest.get('format') != 'r162p-exact-packet-v1' or manifest.get('scope') != 'packet/':
        raise ValueError('unsupported manifest or scope')
    expected = set()
    base = root / 'packet'
    for entry in manifest['files']:
        relative = entry['path']
        parts = relative.split('/')
        if not relative or relative.startswith('/') or any(p in ('', '.', '..') for p in parts):
            raise ValueError('noncanonical manifest path')
        if relative in expected:
            raise ValueError('duplicate manifest entry')
        expected.add(relative)
        path = base.joinpath(*parts)
        current = base
        for component in parts:
            current = current / component
            if current.is_symlink():
                raise ValueError('symlink in manifest path')
        if not path.resolve().is_relative_to(base):
            raise ValueError('manifest path escapes packet')
        if path.stat().st_size != entry['bytes']:
            raise ValueError('packet size mismatch')
        anchor(path, entry['sha256'])
    actual = set()
    for current, directories, files in os.walk(base, followlinks=False):
        for name in directories + files:
            if (Path(current) / name).is_symlink():
                raise ValueError('unmanifested symlink')
        for name in files:
            path = Path(current) / name
            if not path.is_file():
                raise ValueError('nonregular packet object')
            actual.add(path.relative_to(base).as_posix())
    if actual != expected:
        raise ValueError('packet inventory differs from exact manifest')
    print(f'PASS: {len(expected)} exact packet files and all three explicit detached anchors match; read-only integrity only.')

if __name__ == '__main__':
    try:
        run()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
