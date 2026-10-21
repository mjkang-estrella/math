#!/usr/bin/env python3
"""Read-only packet verification. Explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def check_hash(path, expected):
    if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
        raise ValueError('invalid explicit SHA256 anchor')
    if path.is_symlink() or not path.is_file() or digest(path) != expected:
        raise ValueError('identity mismatch: ' + str(path))


def check_entry(root, entry):
    rel = PurePosixPath(entry['path'])
    if rel.is_absolute() or '..' in rel.parts or str(rel) != entry['path']:
        raise ValueError('unsafe manifest path')
    p = root.joinpath(*rel.parts)
    cursor = root
    for part in rel.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise ValueError('symlink in packet path')
    if p.stat().st_size != entry['bytes']:
        raise ValueError('size mismatch: ' + entry['path'])
    check_hash(p, entry['sha256'])


def verify(root, final_anchor, manifest_anchor, report_anchor):
    root = root.resolve()
    if root != Path(__file__).resolve().parent:
        raise ValueError('verifier is limited to its own packet root')
    check_hash(root / 'FINAL.md', final_anchor)
    check_hash(root / 'MANIFEST.json', manifest_anchor)
    check_hash(root / 'REPORT.md', report_anchor)
    m = json.loads((root / 'MANIFEST.json').read_text())
    if m['format'] != 'r142-exact-packet-v1':
        raise ValueError('unexpected manifest format')
    paths = [e['path'] for e in m['files']]
    if len(paths) != len(set(paths)):
        raise ValueError('duplicate manifest paths')
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in packet')
        rel = p.relative_to(root).as_posix()
        if p.is_file() and rel not in ('MANIFEST.json', 'REPORT.md'):
            actual.add(rel)
    if actual != set(paths):
        raise ValueError('packet inventory differs from exact manifest')
    for e in m['files']:
        check_entry(root, e)
    return {'artifact_identity': 'matched', 'files': len(paths),
            'mathematical_gate': False, 'writes': 0}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--final', required=True)
    parser.add_argument('--manifest', required=True)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    print(json.dumps(verify(Path(__file__).parent, args.final, args.manifest, args.report), sort_keys=True))
