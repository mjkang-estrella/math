#!/usr/bin/env python3
"""Read-only exact artifact verifier. Explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
import stat
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    for rel, expected in [('packet/FINAL.md', final_sha),
                          ('MANIFEST.json', manifest_sha),
                          ('REPORT.md', report_sha)]:
        p = root / rel
        if p.is_symlink() or sha(p.read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    rows = manifest['files']
    expected_paths = [r['path'] for r in rows]
    if len(set(expected_paths)) != len(expected_paths):
        raise ValueError('duplicate manifest path')
    for rel in expected_paths:
        q = Path(rel)
        if q.is_absolute() or '..' in q.parts or q.as_posix() != rel:
            raise ValueError('unsafe manifest path')
    packet = root / 'packet'
    if packet.is_symlink():
        raise ValueError('packet is a symlink')
    found = []
    for p in packet.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in packet')
        if p.is_file():
            found.append(p.relative_to(packet).as_posix())
    if sorted(found) != sorted(expected_paths):
        raise ValueError('exact packet membership mismatch')
    for row in rows:
        p = packet / row['path']
        b = p.read_bytes()
        if (len(b) != row['bytes'] or sha(b) != row['sha256'] or
                stat.S_IMODE(p.stat().st_mode) != row['mode']):
            raise ValueError('file identity mismatch: ' + row['path'])
    return len(rows)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    n = verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256)
    print('Artifact verification OK:', n, 'exact files; hashes and modes. No mathematical gate.')
