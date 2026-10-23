#!/usr/bin/env python3
"""Read-only artifact verifier; caller supplies all three detached SHA256 anchors."""
import argparse
import hashlib
import json
import re
from pathlib import Path, PurePosixPath


def digest(path):
    with path.open('rb') as stream:
        h = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
        return h.hexdigest()


def verify(root, final_anchor, manifest_anchor, report_anchor):
    root = Path(root).absolute()
    packet = root / 'packet'
    for path, anchor in [(packet / 'FINAL.md', final_anchor),
                         (packet / 'MANIFEST.json', manifest_anchor),
                         (root / 'REPORT.md', report_anchor)]:
        if not re.fullmatch('[0-9a-f]{64}', anchor):
            raise ValueError('anchor must be an explicit lowercase SHA256')
        if path.is_symlink() or digest(path) != anchor:
            raise ValueError('detached anchor mismatch: ' + path.name)
    if packet.is_symlink():
        raise ValueError('symlink packet')
    manifest = json.loads((packet / 'MANIFEST.json').read_text(encoding='utf-8'))
    if manifest.get('format') != 'arithmetic162b-packet-v1':
        raise ValueError('unknown manifest format')
    expected = set()
    for row in manifest['files']:
        name = row['path']
        rel = PurePosixPath(name)
        if (rel.is_absolute() or '..' in rel.parts or name != rel.as_posix()
                or name in expected or name == 'MANIFEST.json' or '\\' in name):
            raise ValueError('invalid or duplicate manifest path')
        expected.add(name)
        path = packet / name
        if any(x.is_symlink() for x in [path, *path.parents] if x != root.parent):
            raise ValueError('symlink payload')
        if path.stat().st_size != row['bytes'] or digest(path) != row['sha256']:
            raise ValueError('payload mismatch: ' + name)
    actual = set()
    for path in packet.rglob('*'):
        if path.is_symlink():
            raise ValueError('symlink in packet')
        if path.is_file():
            actual.add(path.relative_to(packet).as_posix())
    if 'FINAL.md' not in expected or actual != expected | {'MANIFEST.json'}:
        raise ValueError('packet inventory differs from exact manifest')
    return len(expected)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        count = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        parser.exit(1, 'ARTIFACT REJECTED: ' + str(exc) + '\n')
    print('ARTIFACT VERIFIED:', count, 'payload files; all three explicit anchors match.')
