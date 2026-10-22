#!/usr/bin/env python3
"""Read-only selected-packet verification against three externally supplied anchors.

This checks artifact integrity only. It neither validates nor grades mathematics.
Run with Python -B to disable incidental bytecode creation by the interpreter.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

CARRIERS = {'FINAL.md', 'REPORT.md', 'private/MANIFEST.json', 'ANCHORS.json'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def checked_path(root, relative):
    part = PurePosixPath(relative)
    if part.is_absolute() or '..' in part.parts or str(part) != relative:
        raise ValueError('unsafe or noncanonical manifest path')
    current = root
    for item in part.parts:
        current = current / item
        if current.is_symlink():
            raise ValueError('symlink in packet path: ' + relative)
    if not current.is_file():
        raise ValueError('missing regular file: ' + relative)
    return current

def verify(args):
    root = Path(args.root).absolute()
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be an existing nonsymlink directory')
    anchor_map = {
        'FINAL.md': args.final_sha,
        'private/MANIFEST.json': args.manifest_sha,
        'REPORT.md': args.report_sha,
    }
    for relative, expected in anchor_map.items():
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('anchor must be an explicit lowercase SHA256')
        if digest(checked_path(root, relative).read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + relative)
    manifest = json.loads(checked_path(root, 'private/MANIFEST.json').read_bytes())
    if manifest.get('format') != 'r191-selected-packet-v1':
        raise ValueError('unsupported manifest format')
    selected = set()
    for entry in manifest['files']:
        relative = entry['path']
        if relative in selected or relative in CARRIERS:
            raise ValueError('duplicate or self-referential selected path')
        selected.add(relative)
        data = checked_path(root, relative).read_bytes()
        if len(data) != entry['bytes'] or digest(data) != entry['sha256']:
            raise ValueError('selected payload mismatch: ' + relative)
    actual = set()
    # This traversal is confined to the packet explicitly supplied by the caller.
    for path in root.rglob('*'):
        if path.is_symlink():
            raise ValueError('symlink present in packet')
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    if actual - CARRIERS != selected:
        raise ValueError('selected file set differs from packet files')
    return len(selected)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha', required=True)
    parser.add_argument('--manifest-sha', required=True)
    parser.add_argument('--report-sha', required=True)
    args = parser.parse_args()
    try:
        count = verify(args)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('ARTIFACT MISMATCH: ' + str(exc), file=sys.stderr)
        return 1
    print('ARTIFACT INTEGRITY: three supplied anchors and %d selected files match; no mathematical assessment.' % count)
    return 0

if __name__ == '__main__':
    sys.exit(main())
