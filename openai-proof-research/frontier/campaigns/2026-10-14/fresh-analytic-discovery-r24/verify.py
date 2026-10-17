#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Identity only. Supply the manifest SHA256 from outside this packet."""
import argparse
import hashlib
import json
from pathlib import Path


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, anchor):
    manifest_bytes = (root / 'manifest.json').read_bytes()
    assert sha(manifest_bytes) == anchor, 'external manifest anchor mismatch'
    manifest = json.loads(manifest_bytes)
    files = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    assert not any(p.is_symlink() for p in root.rglob('*')), 'symlink'
    expected = set(manifest['files']) | {'manifest.json'}
    assert files == expected, ('file membership', sorted(files ^ expected))
    dirs = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_dir()}
    assert dirs == set(manifest['directories']), 'directory membership'
    for name, entry in manifest['files'].items():
        data = (root / name).read_bytes()
        assert len(data) == entry['bytes'], ('length', name)
        assert sha(data) == entry['sha256'], ('SHA256', name)
    inventory = json.loads((root / 'family-inventory.json').read_text())
    assert inventory['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    assert inventory['tree_truncated'] is False
    blobs = {item['path']: item['sha'] for item in inventory['blobs']}
    receipts = json.loads((root / 'source-receipt.json').read_text())
    assert len(receipts) == 4
    for entry in receipts:
        data = (root / entry['local']).read_bytes()
        git = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert git == entry['git_blob'] == blobs[entry['path']]
        assert sha(data) == entry['sha256']
    primary = json.loads((root / 'primary-receipt.json').read_text())
    for entry in primary:
        data = (root / 'private/primary' / (entry['name'] + '.pdf')).read_bytes()
        assert sha(data) == entry['sha256'] and len(data) == entry['bytes']
    return dict(status='INTEGRITY_ONLY', payloads=len(manifest['files']),
                pinned_text_blobs=len(receipts), primary_pdfs=len(primary))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    print(json.dumps(verify(Path(__file__).resolve().parent, args.anchor), sort_keys=True))
