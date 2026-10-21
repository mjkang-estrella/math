#!/usr/bin/env python3
"""Read-only exact-membership verifier. Detached anchors must be external inputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def inventory(root):
    files, dirs = {}, []
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    for base, directory_names, names in os.walk(root, topdown=True, followlinks=False):
        directory_names.sort()
        names.sort()
        for n in directory_names:
            p = Path(base) / n
            if p.is_symlink() or not stat.S_ISDIR(p.lstat().st_mode):
                raise ValueError('non-directory or symlink in directory inventory')
            dirs.append(p.relative_to(root).as_posix())
        for n in names:
            p = Path(base) / n
            st = p.lstat()
            if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
                raise ValueError('nonregular, symlink or multiply-linked file')
            rel = p.relative_to(root).as_posix()
            if rel in ENVELOPES:
                continue
            b = p.read_bytes()
            files[rel] = {'bytes': len(b), 'sha256': sha(b)}
    return {'format': 'r128-exact-payload-v1', 'directories': sorted(dirs),
            'files': dict(sorted(files.items()))}

def verify(root, anchors):
    for name, anchor in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', anchor):
            raise ValueError('invalid detached anchor')
        p = root / name
        st = p.lstat()
        if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
            raise ValueError('invalid envelope')
        if sha(p.read_bytes()) != anchor:
            raise ValueError('detached anchor mismatch: ' + name)
    expected = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    actual = inventory(root)
    if actual != expected:
        raise ValueError('payload bytes or exact membership differ')
    return {'artifact_only': True, 'files': len(actual['files']),
            'directories': len(actual['directories']), 'verified': True}

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.root, {'FINAL.md': args.final_sha,
                                           'MANIFEST.json': args.manifest_sha,
                                           'REPORT.md': args.report_sha}), sort_keys=True))
    except (OSError, ValueError, TypeError) as error:
        print(json.dumps({'verified': False, 'error': str(error)}))
        sys.exit(1)
