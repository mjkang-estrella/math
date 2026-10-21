#!/usr/bin/env python3
"""Read-only exact-membership verifier; envelope anchors must come from outside."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    files, directories = {}, []
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    for here, dirs, names in os.walk(root, followlinks=False):
        for name in sorted(dirs):
            p = Path(here) / name
            if not stat.S_ISDIR(p.lstat().st_mode):
                raise ValueError('non-directory or symlink: ' + str(p.relative_to(root)))
            directories.append(p.relative_to(root).as_posix())
        for name in sorted(names):
            p = Path(here) / name
            rel = p.relative_to(root).as_posix()
            if not stat.S_ISREG(p.lstat().st_mode):
                raise ValueError('non-regular file or symlink: ' + rel)
            if rel in ENVELOPES:
                continue
            data = p.read_bytes()
            files[rel] = {'size': len(data), 'sha256': digest(data)}
    return {'files': dict(sorted(files.items())), 'directories': sorted(directories)}

def unique_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('duplicate JSON key: ' + key)
        out[key] = value
    return out

def verify(root, anchors):
    for name, expected in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('invalid detached SHA256: ' + name)
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing/non-regular envelope: ' + name)
        if digest(p.read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text(), object_pairs_hook=unique_object)
    if set(manifest) != {'format', 'excluded_envelopes', 'files', 'directories'}:
        raise ValueError('unexpected manifest schema')
    if manifest['format'] != 'r146-exact-membership-v1' or manifest['excluded_envelopes'] != sorted(ENVELOPES):
        raise ValueError('unexpected manifest format or exclusion set')
    actual = inventory(root)
    if actual['directories'] != manifest['directories']:
        raise ValueError('directory membership mismatch')
    if actual['files'] != manifest['files']:
        raise ValueError('file membership, size, or hash mismatch')
    return {'artifact_integrity': 'verified', 'files': len(actual['files']),
            'directories': len(actual['directories']), 'mathematical_grade': None}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    anchors = {'FINAL.md': args.final_sha256, 'MANIFEST.json': args.manifest_sha256,
               'REPORT.md': args.report_sha256}
    try:
        print(json.dumps(verify(args.root, anchors), sort_keys=True))
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({'artifact_integrity': 'rejected', 'reason': str(error)}))
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
