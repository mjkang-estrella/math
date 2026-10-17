#!/usr/bin/env python3
# Original code: Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only external-anchor and exact-membership verification; no proof verdict."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--anchor', required=True)
    p.add_argument('--check-inputs', action='store_true')
    a = p.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'manifest.json').read_bytes()
    if len(a.anchor) != 64 or sha(raw) != a.anchor:
        raise ValueError('external manifest anchor mismatch')
    m = json.loads(raw)
    paths = list(root.rglob('*'))
    if any(x.is_symlink() for x in paths):
        raise ValueError('symlink prohibited')
    files = {str(x.relative_to(root)) for x in paths if x.is_file()}
    dirs = {str(x.relative_to(root)) for x in paths if x.is_dir()}
    expected = {x['path'] for x in m['files']}
    if len(expected) != len(m['files']):
        raise ValueError('duplicate manifest entry')
    if files != expected | {'manifest.json'} or dirs != set(m['directories']):
        raise ValueError('exact membership mismatch')
    for x in m['files']:
        rel = Path(x['path'])
        if rel.is_absolute() or '..' in rel.parts:
            raise ValueError('unsafe relative path')
        b = (root / rel).read_bytes()
        if len(b) != x['bytes'] or sha(b) != x['sha256']:
            raise ValueError('payload mismatch: ' + x['path'])
    receipts = []
    for name in ['source-receipts.json', 'source171-receipts.json']:
        receipts.extend(json.loads((root / name).read_text()))
    if len(receipts) != 37:
        raise ValueError('unexpected source count')
    for x in receipts:
        b = (root / x['path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        if blob != x['git_blob'] or sha(b) != x['sha256']:
            raise ValueError('pinned source identity mismatch')
    inputs = json.loads((root / 'external-inputs.json').read_text())
    if a.check_inputs:
        repo = root.parents[3]
        for x in inputs:
            b = (repo / x['path']).read_bytes()
            if len(b) != x['bytes'] or sha(b) != x['sha256']:
                raise ValueError('external input mismatch: ' + x['path'])
        tree = json.loads((repo / 'sources/preprints-tree.json').read_text())
        items = tree['tree'] if isinstance(tree, dict) else tree
        indexed = {x['path']: x['sha'] for x in items if x.get('type') == 'blob'}
        for x in receipts:
            key = x['upstream_path']
            if key not in indexed and key.startswith('preprints/'):
                key = key[len('preprints/'):]
            if indexed.get(key) != x['git_blob']:
                raise ValueError('source not at recorded tree path')
    print(json.dumps({'status': 'INTEGRITY_OK', 'payload_files': len(expected),
                      'directories': len(dirs), 'pinned_blobs': len(receipts),
                      'external_inputs_checked': len(inputs) if a.check_inputs else 0,
                      'mathematical_verdict': None}))

if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('REJECT: ' + str(e), file=sys.stderr)
        sys.exit(1)
