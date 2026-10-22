#!/usr/bin/env python3
"""Read-only exact-packet verifier. Supply detached hashes explicitly; never reseals."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def verify(root, final_sha, manifest_sha, report_sha):
    packet = root / 'packet'
    for p in (root, packet, root / 'MANIFEST.json', root / 'REPORT.md', packet / 'FINAL.md'):
        if p.is_symlink():
            raise ValueError('symlink anchor or root: ' + str(p))
    for p, expected in ((packet / 'FINAL.md', final_sha),
                        (root / 'MANIFEST.json', manifest_sha),
                        (root / 'REPORT.md', report_sha)):
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('anchor must be explicit lowercase SHA256')
        if digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + p.name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    if manifest.get('format') != 'r158-exact-packet-v1':
        raise ValueError('unsupported manifest format')
    expected_paths = {}
    for row in manifest['files']:
        rel = row['path']
        pp = PurePosixPath(rel)
        if pp.is_absolute() or '..' in pp.parts or str(pp) != rel or '\\' in rel or not pp.parts:
            raise ValueError('unsafe/noncanonical relative manifest path')
        if rel in expected_paths:
            raise ValueError('duplicate manifest path')
        expected_paths[rel] = row
    actual = set()
    total = 0
    for d, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            p = Path(d) / name
            mode = p.lstat().st_mode
            if stat.S_ISLNK(mode):
                raise ValueError('packet symlink: ' + str(p.relative_to(packet)))
            if not (stat.S_ISDIR(mode) or stat.S_ISREG(mode)):
                raise ValueError('nonregular packet entry')
        for name in files:
            p = Path(d) / name
            rel = p.relative_to(packet).as_posix()
            actual.add(rel)
            if rel not in expected_paths:
                raise ValueError('unlisted packet file: ' + rel)
            row = expected_paths[rel]
            b = p.read_bytes()
            if len(b) != row['bytes'] or hashlib.sha256(b).hexdigest() != row['sha256']:
                raise ValueError('packet content mismatch: ' + rel)
            total += len(b)
    if actual != set(expected_paths):
        raise ValueError('missing packet files: ' + ','.join(sorted(set(expected_paths) - actual)))
    if 'FINAL.md' not in actual:
        raise ValueError('FINAL absent from manifest')
    if manifest.get('file_count') != len(actual) or manifest.get('total_bytes') != total:
        raise ValueError('manifest totals mismatch')
    return {'artifact_integrity': 'matched explicit anchors and exact file set',
            'files': len(actual), 'bytes': total, 'mathematical_grade': 'not assigned'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True, type=Path)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        result = verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({'artifact_integrity': 'rejected', 'reason': str(exc)}))
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
