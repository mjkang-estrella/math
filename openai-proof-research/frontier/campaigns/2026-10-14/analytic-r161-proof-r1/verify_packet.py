#!/usr/bin/env python3
"""Read-only exact selected-packet verification using independent envelope anchors."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import stat

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, anchors):
    root = Path(root)
    for name in ENVELOPES:
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or symlink envelope: ' + name)
        if digest(p.read_bytes()) != anchors[name]:
            raise ValueError('envelope hash mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest['format'] != 'analytic-r161-proof-r1-selected-v1':
        raise ValueError('unexpected manifest format')
    if set(manifest['outside_envelopes']) != ENVELOPES:
        raise ValueError('unexpected envelope exclusions')
    expected = {}
    for row in manifest['files']:
        s = row['path']
        p = Path(s)
        if p.is_absolute() or '..' in p.parts or s in ENVELOPES or s in expected:
            raise ValueError('unsafe or duplicate payload path: ' + s)
        expected[s] = row
    actual = {}
    directories = set()
    for current, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            p = Path(current) / name
            if p.is_symlink():
                raise ValueError('symlink: ' + str(p.relative_to(root)))
        for name in dirs:
            directories.add((Path(current) / name).relative_to(root).as_posix())
        for name in files:
            p = Path(current) / name
            s = p.relative_to(root).as_posix()
            if s not in ENVELOPES:
                actual[s] = p
    if set(actual) != set(expected):
        raise ValueError('payload membership mismatch; missing=' + repr(sorted(set(expected)-set(actual))) + '; extra=' + repr(sorted(set(actual)-set(expected))))
    expected_dirs = {parent.as_posix() for s in expected for parent in Path(s).parents if parent != Path('.')}
    if directories != expected_dirs:
        raise ValueError('directory membership mismatch')
    for s, p in actual.items():
        row = expected[s]
        b = p.read_bytes()
        if len(b) != row['bytes'] or digest(b) != row['sha256']:
            raise ValueError('payload byte mismatch: ' + s)
        if stat.S_IMODE(p.stat().st_mode) != row['mode']:
            raise ValueError('payload mode mismatch: ' + s)
    return len(actual)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    anchors = {'FINAL.md': args.final_sha256, 'MANIFEST.json': args.manifest_sha256, 'REPORT.md': args.report_sha256}
    try:
        n = verify(args.root, anchors)
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        parser.exit(1, 'INVALID: ' + str(exc) + '\n')
    print(f'VALID: {n} exact payload files plus 3 independently anchored outside envelopes; integrity only')

if __name__ == '__main__':
    main()
