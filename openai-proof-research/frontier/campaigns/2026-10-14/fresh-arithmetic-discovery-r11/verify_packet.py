#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only externally anchored integrity check; no mathematical verdict."""
import argparse
import hashlib
import json
from pathlib import Path

def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'manifest.json').read_bytes()
    require(sha(raw) == args.seal_sha256, 'external seal mismatch')
    manifest = json.loads(raw)
    paths = list(root.rglob('*'))
    require(not any(p.is_symlink() for p in paths), 'symlink')
    files = {p.relative_to(root).as_posix() for p in paths if p.is_file()}
    dirs = {p.relative_to(root).as_posix() for p in paths if p.is_dir()}
    require(files == set(manifest['files']) | {'manifest.json'}, 'file membership')
    require(dirs == set(manifest['directories']), 'directory membership')
    for name, expected in manifest['files'].items():
        require(sha((root / name).read_bytes()) == expected, 'digest: ' + name)
    receipts = json.loads((root / 'source-receipts.json').read_text())
    for receipt in receipts:
        data = (root / receipt['local']).read_bytes()
        identity = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(identity == receipt['git_blob'], 'Git blob: ' + receipt['path'])
        require(sha(data) == receipt['sha256'], 'source digest: ' + receipt['path'])
    print(json.dumps({'integrity': 'PASS', 'payload_files': len(manifest['files']),
                      'directories': len(dirs), 'pinned_blobs': len(receipts),
                      'status': manifest['status'], 'mathematical_verdict': None}))

if __name__ == '__main__':
    main()
