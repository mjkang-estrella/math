#!/usr/bin/env python3
"""Read-only exact-packet verification against three explicitly supplied anchors."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def verify(root, final_hash, manifest_hash, report_hash):
    root = root.resolve(strict=True)
    for name, expected in [('FINAL.md', final_hash), ('MANIFEST.json', manifest_hash), ('REPORT.md', report_hash)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit anchor: ' + name)
        p = root / name
        if p.is_symlink() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    doc = json.loads((root / 'MANIFEST.json').read_bytes())
    if doc.get('format') != 'r145-exact-packet-v1':
        raise ValueError('manifest format')
    entries = doc['files']
    seen = set()
    for item in entries:
        name = item['path']
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or not rel.parts or rel.as_posix() != name:
            raise ValueError('unsafe manifest path')
        if name in seen or name in {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}:
            raise ValueError('duplicate or envelope path')
        seen.add(name)
        p = root / rel
        if any((root / Path(*rel.parts[:i])).is_symlink() for i in range(1, len(rel.parts)+1)):
            raise ValueError('symlink in packet')
        if p.stat().st_size != item['bytes'] or digest(p) != item['sha256']:
            raise ValueError('payload mismatch: ' + name)
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in packet inventory')
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    actual -= {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
    if actual != seen:
        raise ValueError('exact membership mismatch')
    if 'FINAL.md' not in seen:
        raise ValueError('FINAL missing from payload')
    return {'artifact_verification': 'matched', 'payload_files': len(seen), 'mathematical_gate': False}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', required=True)
    ap.add_argument('--final', required=True)
    ap.add_argument('--manifest', required=True)
    ap.add_argument('--report', required=True)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(Path(args.root), args.final, args.manifest, args.report), sort_keys=True))
    except Exception as exc:
        ap.exit(1, str(exc) + '\n')
