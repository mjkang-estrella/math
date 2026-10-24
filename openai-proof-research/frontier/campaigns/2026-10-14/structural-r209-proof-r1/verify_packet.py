#!/usr/bin/env python3
"""Read-only artifact verification with three explicit detached SHA256 anchors.

Adapted from the inspected author r209 verifier: schema identifier changed;
verification logic unchanged. Only the supplied packet root is traversed. This verifies bytes, selection and
POSIX modes, not mathematics, authenticity of rights, or review outcomes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

OUTSIDE = {'MANIFEST.json', 'REPORT.md', 'DETACHED-ANCHORS.json'}
ANCHOR_NAMES = ('FINAL.md', 'MANIFEST.json', 'REPORT.md')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_relative(value):
    require(isinstance(value, str), 'non-string path')
    p = PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == value,
            'unsafe or noncanonical path: ' + value)
    require(value not in ('', '.'), 'invalid file path')
    return value


def inventory(root):
    files, directories = {}, {'.': stat.S_IMODE(root.lstat().st_mode)}
    require(stat.S_ISDIR(root.lstat().st_mode), 'packet root is not a plain directory')
    def visit(directory):
        with os.scandir(directory) as it:
            entries = sorted(it, key=lambda e: e.name)
        for entry in entries:
            p = Path(entry.path)
            relative = p.relative_to(root).as_posix()
            st = entry.stat(follow_symlinks=False)
            require(not stat.S_ISLNK(st.st_mode), 'symlink forbidden: ' + relative)
            if stat.S_ISDIR(st.st_mode):
                directories[relative] = stat.S_IMODE(st.st_mode)
                visit(p)
            else:
                require(stat.S_ISREG(st.st_mode), 'nonregular entry: ' + relative)
                files[relative] = {'bytes': st.st_size,
                                   'sha256': sha(p.read_bytes()),
                                   'mode': stat.S_IMODE(st.st_mode)}
    visit(root)
    return files, directories


def verify(root, anchors):
    require(set(anchors) == set(ANCHOR_NAMES), 'wrong detached anchor names')
    require(all(re.fullmatch('[0-9a-f]{64}', v) for v in anchors.values()),
            'anchors must be explicit lowercase SHA256 values')
    files, directories = inventory(root)
    for name, anchor in anchors.items():
        require(name in files, 'missing anchor file: ' + name)
        require(files[name]['sha256'] == anchor, 'detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    require(manifest['schema'] == 'review-r209-exact-packet-v1', 'wrong manifest schema')
    expected_files = {}
    for item in manifest['selected_files']:
        name = safe_relative(item['path'])
        require(name not in expected_files and name not in OUTSIDE, 'duplicate/outside selection: ' + name)
        expected_files[name] = {k: item[k] for k in ('bytes', 'sha256', 'mode')}
    require('FINAL.md' in expected_files, 'FINAL must be selected')
    outside = {}
    for item in manifest['outside_files']:
        name = safe_relative(item['path'])
        require(name not in outside, 'duplicate outside file')
        outside[name] = item['mode']
    require(set(outside) == OUTSIDE, 'outside selection differs')
    require(set(files) == set(expected_files) | OUTSIDE, 'exact file selection mismatch')
    for name, expected in expected_files.items():
        require(files[name] == expected, 'selected bytes/mode mismatch: ' + name)
    for name, mode in outside.items():
        require(files[name]['mode'] == mode, 'outside mode mismatch: ' + name)
    expected_directories = {}
    for item in manifest['directories']:
        name = item['path']
        if name != '.':
            safe_relative(name)
        require(name not in expected_directories, 'duplicate directory')
        expected_directories[name] = item['mode']
    require(directories == expected_directories, 'exact directory selection/mode mismatch')
    require(json.loads((root / 'DETACHED-ANCHORS.json').read_bytes()) == anchors,
            'detached display file disagrees with explicit anchors')
    return {'artifact_verification': 'PASS',
            'selected_files': len(expected_files), 'outside_files': len(OUTSIDE),
            'directories_including_root': len(directories),
            'selected_bytes': sum(x['bytes'] for x in expected_files.values()),
            'mathematical_gate': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    anchors = dict(zip(ANCHOR_NAMES, (args.final_sha256, args.manifest_sha256, args.report_sha256)))
    try:
        print(json.dumps(verify(args.root.absolute(), anchors), sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({'artifact_verification': 'FAIL', 'reason': str(exc)}))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
