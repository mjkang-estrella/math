#!/usr/bin/env python3
"""Read-only artifact verification. Supply all three detached anchors explicitly."""
import argparse
import hashlib
import json
import sys
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root).resolve(strict=True)
    for rel, expected in [('packet/FINAL.md', final_sha), ('MANIFEST.json', manifest_sha), ('REPORT.md', report_sha)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit anchor: ' + rel)
        path = root / rel
        if path.is_symlink() or digest(path.read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    if manifest.get('format') != 'arithmetic162d-packet-v1':
        raise ValueError('unexpected manifest format')
    entries = manifest['files']
    expected_paths = set()
    for entry in entries:
        name = entry['path']
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or str(rel) != name or not name.startswith('packet/'):
            raise ValueError('unsafe manifest path')
        if name in expected_paths:
            raise ValueError('duplicate manifest path')
        expected_paths.add(name)
        path = root / name
        for ancestor in [path, *path.parents]:
            if ancestor == root:
                break
            if ancestor.is_symlink():
                raise ValueError('symlink in selected packet: ' + name)
        data = path.read_bytes()
        if len(data) != entry['bytes'] or digest(data) != entry['sha256']:
            raise ValueError('selected file mismatch: ' + name)
    actual_paths = set()
    for path in (root / 'packet').rglob('*'):
        if path.is_symlink():
            raise ValueError('symlink in packet')
        if path.is_file():
            actual_paths.add(path.relative_to(root).as_posix())
    if actual_paths != expected_paths or 'packet/FINAL.md' not in expected_paths:
        raise ValueError('selected file-set mismatch')
    return len(entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        count = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('ARTIFACT MISMATCH: ' + str(exc), file=sys.stderr)
        return 1
    print('Artifact bytes and explicit anchors match; selected files:', count)
    print('No mathematical assessment performed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
