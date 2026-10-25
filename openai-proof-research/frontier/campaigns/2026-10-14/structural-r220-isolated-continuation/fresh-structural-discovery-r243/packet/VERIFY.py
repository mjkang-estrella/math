#!/usr/bin/env python3
"""Read-only exact-selection verifier; all detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser()
    for name in ('packet', 'manifest', 'report', 'final-sha256', 'manifest-sha256', 'report-sha256'):
        ap.add_argument('--' + name, required=True)
    a = ap.parse_args()
    for value in (a.final_sha256, a.manifest_sha256, a.report_sha256):
        require(re.fullmatch('[0-9a-f]{64}', value), 'invalid explicit anchor')
    root = Path(a.packet)
    require(root.is_dir() and not root.is_symlink(), 'packet must be a real directory')
    raw = Path(a.manifest).read_bytes()
    require(sha(raw) == a.manifest_sha256, 'manifest anchor mismatch')
    require(sha(Path(a.report).read_bytes()) == a.report_sha256, 'report anchor mismatch')
    m = json.loads(raw)
    require(m['format'] == 'r243-exact-selection-v1', 'unknown manifest format')
    files, dirs = {}, {}
    for base, directory_names, file_names in os.walk(root, followlinks=False):
        p = Path(base)
        relative = p.relative_to(root).as_posix()
        dirs[relative] = format(stat.S_IMODE(p.stat().st_mode), '04o')
        for name in directory_names + file_names:
            require(not (p / name).is_symlink(), 'symlink in packet')
        for name in file_names:
            q = p / name
            require(stat.S_ISREG(q.stat().st_mode), 'nonregular packet entry')
            files[q.relative_to(root).as_posix()] = q
    expected = {item['path']: item for item in m['files']}
    require(len(expected) == len(m['files']), 'duplicate manifest path')
    require(set(files) == set(expected), 'exact file selection mismatch')
    require(dirs == m['directories'], 'directory selection or mode mismatch')
    total = 0
    for rel, item in expected.items():
        pp = PurePosixPath(rel)
        require(not pp.is_absolute() and '..' not in pp.parts and str(pp) == rel,
                'unsafe or noncanonical manifest path')
        p = files[rel]
        require(format(stat.S_IMODE(p.stat().st_mode), '04o') == item['mode'],
                'file mode mismatch: ' + rel)
        data = p.read_bytes()
        require(len(data) == item['bytes'] and sha(data) == item['sha256'],
                'content mismatch: ' + rel)
        total += len(data)
    require('FINAL.md' in expected, 'FINAL.md absent')
    require(sha(files['FINAL.md'].read_bytes()) == a.final_sha256, 'FINAL anchor mismatch')
    print(json.dumps({'ok': True, 'files': len(files), 'bytes': total,
                      'read_only': True, 'exact_selection_and_modes': True}))

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'ok': False, 'error': str(error)}))
        sys.exit(2)
