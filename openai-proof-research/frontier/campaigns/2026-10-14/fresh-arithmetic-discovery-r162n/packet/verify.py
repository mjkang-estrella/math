#!/usr/bin/env python3
"""Read-only exact-packet verifier. Detached anchors are mandatory caller inputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

ANCHORS = ('FINAL.md', 'MANIFEST.json', 'REPORT.md')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    files = []
    directories = []
    for here, dirs, names in os.walk(root, followlinks=False):
        for name in dirs:
            p = Path(here) / name
            if not stat.S_ISDIR(p.lstat().st_mode):
                raise ValueError('Non-directory or symlink: ' + str(p.relative_to(root)))
            directories.append(p.relative_to(root).as_posix())
        for name in names:
            p = Path(here) / name
            rel = p.relative_to(root).as_posix()
            info = p.lstat()
            if not stat.S_ISREG(info.st_mode):
                raise ValueError('Non-regular file: ' + rel)
            if rel in ANCHORS:
                continue
            data = p.read_bytes()
            files.append({'path': rel, 'bytes': len(data), 'sha256': sha(data),
                          'mode': stat.S_IMODE(info.st_mode)})
    return {'schema': 1, 'anchor_exclusions': list(ANCHORS),
            'directories': sorted(directories),
            'files': sorted(files, key=lambda x: x['path'])}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    root = Path(args.root)
    try:
        if root.is_symlink() or not root.is_dir():
            raise ValueError('Root must be an actual directory')
        root = root.resolve()
        for name, expected in zip(ANCHORS, (args.final_sha256, args.manifest_sha256, args.report_sha256)):
            if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
                raise ValueError('Expected anchor must be lowercase SHA256: ' + name)
            p = root / name
            if not stat.S_ISREG(p.lstat().st_mode):
                raise ValueError('Non-regular anchor: ' + name)
            if sha(p.read_bytes()) != expected:
                raise ValueError('Detached anchor mismatch: ' + name)
        expected = json.loads((root / 'MANIFEST.json').read_bytes())
        actual = inventory(root)
        if expected != actual:
            raise ValueError('Exact payload inventory/content/mode mismatch')
        print('Artifact integrity matches all three supplied anchors and exact payload inventory.')
        print('This is not a mathematical correctness or contribution gate.')
        return 0
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print('Artifact verification failed: ' + str(exc), file=sys.stderr)
        return 1

if __name__ == '__main__':
    sys.exit(main())
