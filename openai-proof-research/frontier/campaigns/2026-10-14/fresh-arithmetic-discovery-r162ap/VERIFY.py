#!/usr/bin/env python3
"""Read-only verification of this exact packet using detached explicit anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path

EXCLUDED = {'private/MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def check_blob(data, expected):
    if digest(data) != expected:
        raise ValueError('SHA256 mismatch')

def inventory(root):
    files, dirs = [], []
    for base, names, leaves in os.walk(root, followlinks=False):
        for name in names + leaves:
            p = Path(base) / name
            if p.is_symlink():
                raise ValueError('Symlink not permitted in packet')
        dirs.extend((Path(base) / n).relative_to(root).as_posix() for n in names)
        files.extend((Path(base) / n).relative_to(root).as_posix() for n in leaves)
    return sorted(files), sorted(dirs)

def controls(root):
    p = root / 'private/integrity-controls'
    original = (p / 'original.txt').read_bytes()
    copied = (p / 'copied.txt').read_bytes()
    altered = (p / 'altered.txt').read_bytes()
    check_blob(copied, digest(original))
    try:
        check_blob(altered, digest(original))
    except ValueError:
        pass
    else:
        raise ValueError('Altered control unexpectedly accepted')

def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--manifest-sha')
    ap.add_argument('--final-sha')
    ap.add_argument('--report-sha')
    ap.add_argument('--controls-only', action='store_true')
    args = ap.parse_args()
    root = Path(args.root).resolve(strict=True)
    controls(root)
    if args.controls_only:
        print('Tiny copied/altered controls passed; no packet or mathematical gate claimed.')
        return
    expected = {'MANIFEST': args.manifest_sha, 'FINAL': args.final_sha, 'REPORT': args.report_sha}
    if any(not v or len(v) != 64 or any(c not in '0123456789abcdef' for c in v) for v in expected.values()):
        ap.error('Provide all three explicit lowercase detached SHA256 anchors')
    for name, rel in [('MANIFEST','private/MANIFEST.json'), ('FINAL','private/FINAL.md'), ('REPORT','REPORT.md')]:
        check_blob((root / rel).read_bytes(), expected[name])
    manifest = json.loads((root / 'private/MANIFEST.json').read_text())
    files, dirs = inventory(root)
    entries = manifest['files']
    if set(files) - EXCLUDED != set(entries) or dirs != manifest['directories']:
        raise ValueError('Exact packet membership mismatch')
    if not EXCLUDED.issubset(set(files)):
        raise ValueError('Detached anchor/report file missing')
    for rel, entry in entries.items():
        if Path(rel).is_absolute() or '..' in Path(rel).parts:
            raise ValueError('Unsafe manifest path')
        data = (root / rel).read_bytes()
        if len(data) != entry['bytes']:
            raise ValueError('Byte-length mismatch: ' + rel)
        check_blob(data, entry['sha256'])
    if json.loads((root / 'ANCHORS.json').read_text()) != expected:
        raise ValueError('Detached anchor copy mismatch')
    print(f'Exact packet verified: {len(entries)} payload files. Read-only artifact verification; no mathematical gate.')

if __name__ == '__main__':
    main()
