#!/usr/bin/env python3
"""Read-only exact-byte membership verifier; three detached anchors required.
No mathematical, permissions, hardlink, empty-directory or access-time claim.
"""
import argparse
import hashlib
import json
import os
import stat
from pathlib import Path, PurePosixPath

ENVELOPES = ['FINAL.md', 'MANIFEST.json', 'REPORT.md']
def digest(data):
    return hashlib.sha256(data).hexdigest()
def inventory(root):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a nonsymlink directory')
    found = {}
    for base, dirs, names in os.walk(root, followlinks=False):
        for name in dirs:
            if (Path(base)/name).is_symlink():
                raise ValueError('directory symlink')
        for name in names:
            p = Path(base)/name
            if p.is_symlink() or not stat.S_ISREG(p.lstat().st_mode):
                raise ValueError('nonregular member')
            data = p.read_bytes()
            found[p.relative_to(root).as_posix()] = {'size': len(data), 'sha256': digest(data)}
    return found

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root')
    for key in ['final', 'manifest', 'report']:
        parser.add_argument('--'+key+'-sha256', required=True)
    args = parser.parse_args()
    root = Path(args.root)
    actual = inventory(root)
    anchors = [args.final_sha256, args.manifest_sha256, args.report_sha256]
    for name, anchor in zip(ENVELOPES, anchors):
        if len(anchor) != 64 or any(c not in '0123456789abcdef' for c in anchor):
            raise ValueError('invalid anchor')
        if actual.get(name, {}).get('sha256') != anchor:
            raise ValueError('detached anchor mismatch: '+name)
    manifest = json.loads((root/'MANIFEST.json').read_bytes())
    if manifest['excluded_envelopes'] != ENVELOPES:
        raise ValueError('envelope policy')
    expected = {}
    for row in manifest['files']:
        name = row['path']
        path = PurePosixPath(name)
        if path.is_absolute() or '..' in path.parts or str(path) != name or name in expected or name in ENVELOPES:
            raise ValueError('invalid or duplicate member')
        expected[name] = {'size': row['size'], 'sha256': row['sha256']}
    payload = {k:v for k,v in actual.items() if k not in ENVELOPES}
    if payload != expected:
        raise ValueError('payload bytes or exact membership mismatch')
    print(json.dumps({'integrity': 'matched', 'payload_files': len(payload),
                      'whole_root_files': len(actual), 'read_only': True,
                      'mathematical_gate': False}))
if __name__ == '__main__':
    main()
