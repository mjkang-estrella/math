#!/usr/bin/env python3
"""Read-only exact-membership verifier. Detached anchors are mandatory inputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inspect(root):
    files = {}
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in dirs + names:
            p = Path(base) / name
            st = p.lstat()
            if stat.S_ISLNK(st.st_mode):
                raise ValueError('symlink: ' + str(p.relative_to(root)))
            if p.is_dir():
                continue
            if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
                raise ValueError('nonregular or hardlinked: ' + str(p.relative_to(root)))
            files[p.relative_to(root).as_posix()] = p
    return files

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    for k in ['final', 'manifest', 'report']:
        ap.add_argument('--' + k + '-sha256', required=True)
    a = ap.parse_args()
    root = Path(a.root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('invalid root')
    files = inspect(root)
    for name, expected in [('FINAL.md', a.final_sha256), ('MANIFEST.json', a.manifest_sha256), ('REPORT.md', a.report_sha256)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid detached anchor: ' + name)
        if name not in files or sha(files[name].read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads(files['MANIFEST.json'].read_text())
    if manifest.get('format') != 'r152-exact-payload-v1' or set(manifest.get('outside_envelopes', [])) != ENVELOPES:
        raise ValueError('manifest format')
    entries = manifest['files']
    expected_paths = set()
    for rec in entries:
        s = rec['path']; p = PurePosixPath(s)
        if p.is_absolute() or '..' in p.parts or p.as_posix() != s or s in ENVELOPES or s in expected_paths:
            raise ValueError('invalid or duplicate member: ' + s)
        expected_paths.add(s)
    if set(files) - ENVELOPES != expected_paths:
        raise ValueError('exact payload membership mismatch')
    for rec in entries:
        b = files[rec['path']].read_bytes()
        if len(b) != rec['bytes'] or sha(b) != rec['sha256']:
            raise ValueError('payload mismatch: ' + rec['path'])
    print(json.dumps({'artifact_check': 'verified', 'payload_files': len(entries), 'mathematical_gate': False}))

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('VERIFICATION ERROR: ' + str(exc), file=sys.stderr)
        sys.exit(1)
