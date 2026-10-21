#!/usr/bin/env python3
"""Read-only exact-packet check. Detached hashes must be supplied by the caller."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import stat

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def mode(path):
    return format(stat.S_IMODE(path.stat().st_mode), '04o')

def inventory(root):
    files, dirs = [], []
    for p in sorted(root.rglob('*')):
        if p.is_symlink():
            raise ValueError('symlink is not permitted: ' + str(p))
        rel = p.relative_to(root).as_posix()
        if p.is_dir():
            dirs.append({'path': rel, 'mode': mode(p)})
        elif p.is_file():
            if rel not in ENVELOPES:
                files.append({'path': rel, 'mode': mode(p),
                              'bytes': p.stat().st_size, 'sha256': digest(p)})
        else:
            raise ValueError('nonregular packet object: ' + rel)
    return files, dirs

def verify(root, anchors):
    for name, expected in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('invalid explicit anchor for ' + name)
        p = root / name
        if p.is_symlink() or not p.is_file() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    obj = json.loads((root / 'MANIFEST.json').read_text())
    if obj.get('schema') != 'r162-exact-packet-v1':
        raise ValueError('unknown manifest schema')
    if mode(root) != obj['root_mode']:
        raise ValueError('root mode mismatch')
    for name in ENVELOPES:
        if mode(root / name) != obj['envelope_modes'][name]:
            raise ValueError('envelope mode mismatch: ' + name)
    files, dirs = inventory(root)
    if files != obj['files'] or dirs != obj['directories']:
        raise ValueError('exact membership, mode, byte length or payload hash mismatch')
    return len(files)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    try:
        count = verify(args.root, {'FINAL.md': args.final_sha256,
                                  'MANIFEST.json': args.manifest_sha256,
                                  'REPORT.md': args.report_sha256})
    except (ValueError, OSError, KeyError, TypeError) as exc:
        ap.exit(1, 'INVALID: ' + str(exc) + '\n')
    print('Artifact integrity only: exact packet verified (%d payload files).' % count)
