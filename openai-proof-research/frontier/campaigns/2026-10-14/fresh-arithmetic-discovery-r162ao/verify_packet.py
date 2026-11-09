#!/usr/bin/env python3
"""Read-only verification. All three detached SHA256 anchors are mandatory."""
import argparse
import hashlib
import json
from pathlib import Path
import stat
import sys


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def verify(root, final_hash, manifest_hash, report_hash):
    root = Path(root).resolve(strict=True)
    special = {'private/MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
    for rel, expected in [('private/FINAL.md', final_hash),
                          ('private/MANIFEST.json', manifest_hash),
                          ('REPORT.md', report_hash)]:
        p = root / rel
        if p.is_symlink() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'private/MANIFEST.json').read_text())
    if manifest['schema'] != 'r162ao-own-packet-v1':
        raise ValueError('unknown schema')
    entries = manifest['files']
    names = [e['path'] for e in entries]
    if len(names) != len(set(names)):
        raise ValueError('duplicate manifest path')
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink rejected')
        if p.is_file():
            rel = p.relative_to(root).as_posix()
            if rel not in special:
                actual.add(rel)
    if actual != set(names):
        raise ValueError('packet membership mismatch')
    total = 0
    for e in entries:
        p = root / e['path']
        if p.resolve().parent != root and root not in p.resolve().parents:
            raise ValueError('path outside packet')
        if p.stat().st_size != e['bytes'] or digest(p) != e['sha256']:
            raise ValueError('payload mismatch: ' + e['path'])
        if stat.S_IMODE(p.stat().st_mode) != e['mode']:
            raise ValueError('mode mismatch: ' + e['path'])
        total += e['bytes']
    return {'files': len(entries), 'bytes': total,
            'anchors': 'matched', 'membership': 'exact', 'read_only': True}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.root, args.final_sha256,
                                args.manifest_sha256, args.report_sha256)))
    except (OSError, ValueError, KeyError) as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
