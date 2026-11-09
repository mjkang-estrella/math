#!/usr/bin/env python3
"""Read-only exact-membership verifier; explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(packet, report, final_sha, manifest_sha, report_sha):
    for value in (final_sha, manifest_sha, report_sha):
        if len(value) != 64 or any(c not in '0123456789abcdef' for c in value):
            raise ValueError('Each explicit anchor must be a lowercase SHA256')
    if packet.is_symlink() or report.is_symlink():
        raise ValueError('Symlink anchor target')
    for path, expected in ((packet/'FINAL.md', final_sha),
                           (packet/'MANIFEST.json', manifest_sha),
                           (report, report_sha)):
        if path.is_symlink() or digest(path) != expected:
            raise ValueError('Detached anchor mismatch: ' + str(path))
    manifest = json.loads((packet/'MANIFEST.json').read_text())
    entries = manifest['files']
    expected_paths = set()
    for item in entries:
        name = item['path']
        p = PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts or str(p) != name or name == 'MANIFEST.json':
            raise ValueError('Unsafe/noncanonical member')
        if name in expected_paths:
            raise ValueError('Duplicate member')
        expected_paths.add(name)
    observed = set()
    for directory, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            p = Path(directory)/name
            if p.is_symlink():
                raise ValueError('Symlink member')
        for name in files:
            p = Path(directory)/name
            if not stat.S_ISREG(p.stat().st_mode):
                raise ValueError('Nonregular member')
            observed.add(p.relative_to(packet).as_posix())
    if observed != expected_paths | {'MANIFEST.json'}:
        raise ValueError('Exact membership mismatch')
    for item in entries:
        p = packet/item['path']
        if p.stat().st_size != item['bytes'] or digest(p) != item['sha256']:
            raise ValueError('Member bytes mismatch: ' + item['path'])
        if stat.S_IMODE(p.stat().st_mode) != item['mode']:
            raise ValueError('Member mode mismatch: ' + item['path'])
    return len(entries)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    args = ap.parse_args()
    try:
        count = verify(args.packet, args.report, args.final_sha, args.manifest_sha, args.report_sha)
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('INVALID: ' + str(error), file=sys.stderr)
        return 1
    print(f'VALID: {count} exact members, bytes/modes and three explicit detached anchors')
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
