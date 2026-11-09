#!/usr/bin/env python3
"""Read-only exact-file verifier. Supply all three detached anchors externally."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

ENVELOPES = {'FINAL.json', 'MANIFEST.json', 'REPORT.md', 'SHA256SUMS'}
FORMAT = 't177c143-contribution-r1-exact-v1'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def safe_path(name):
    require(isinstance(name, str) and bool(name), 'invalid path')
    p = PurePosixPath(name)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == name, 'unsafe path')
    return name

def check(root, anchors):
    root = Path(root).absolute()
    require(root.is_dir() and not root.is_symlink(), 'invalid root')
    actual = set()
    for d, ds, fs in os.walk(root, followlinks=False):
        for name in ds + fs:
            require(not (Path(d)/name).is_symlink(), 'symlink')
        for name in fs:
            actual.add((Path(d)/name).relative_to(root).as_posix())
    require(set(anchors) == {'FINAL.json', 'MANIFEST.json', 'REPORT.md'}, 'three anchors required')
    for name, value in anchors.items():
        require(isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value), 'invalid digest')
        require(name in actual and digest((root/name).read_bytes()) == value, 'anchor mismatch: '+name)
    manifest = json.loads((root/'MANIFEST.json').read_text())
    final = json.loads((root/'FINAL.json').read_text())
    require(manifest['format'] == FORMAT, 'format')
    require(final['manifest_sha256'] == anchors['MANIFEST.json'], 'manifest linkage')
    require(final['report_sha256'] == anchors['REPORT.md'], 'report linkage')
    paths = set()
    for row in manifest['files']:
        name = safe_path(row['path'])
        require(name not in paths and name not in ENVELOPES, 'duplicate/envelope')
        paths.add(name)
        require(name in actual, 'missing payload: '+name)
        data = (root/name).read_bytes()
        require(len(data) == row['bytes'] and digest(data) == row['sha256'], 'payload mismatch: '+name)
    require(actual == paths | ENVELOPES, 'file membership mismatch')
    for prefix in ['verifier', 'review']:
        name = safe_path(final[prefix+'_path'])
        require(name in paths and digest((root/name).read_bytes()) == final[prefix+'_sha256'], prefix+' linkage')
    expected = ''.join(anchors[n]+'  '+n+'\n' for n in ['FINAL.json', 'MANIFEST.json', 'REPORT.md'])
    require((root/'SHA256SUMS').read_text() == expected, 'detached list')
    return len(paths)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('root')
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    try:
        n = check(a.root, {'FINAL.json':a.final_sha256, 'MANIFEST.json':a.manifest_sha256, 'REPORT.md':a.report_sha256})
    except (OSError, ValueError, KeyError, TypeError) as e:
        print('FAIL:', e)
        return 1
    print('OK:', n, 'payload files; exact hashes/membership; no mathematical verdict.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
