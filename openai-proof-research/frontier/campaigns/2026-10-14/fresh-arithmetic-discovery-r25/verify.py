#!/usr/bin/env python3
"""Read-only sealed-inventory checker; no semantic acceptance.
Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""
import argparse
import hashlib
import json
from pathlib import Path
import runpy

def digest(b):
    return hashlib.sha256(b).hexdigest()

def verify(root, anchor):
    manifest = root / 'MANIFEST.json'
    assert not manifest.is_symlink(), 'manifest symlink'
    raw = manifest.read_bytes()
    assert digest(raw) == anchor, 'external anchor mismatch'
    data = json.loads(raw)
    actual = {}
    for p in root.iterdir():
        if p.name == 'private':
            assert not p.is_symlink(), 'private symlink'
            continue
        assert not p.is_symlink(), 'symlink: ' + p.name
        assert p.is_file(), 'unexpected directory: ' + p.name
        if p.name != 'MANIFEST.json':
            actual[p.name] = {'bytes': p.stat().st_size, 'sha256': digest(p.read_bytes())}
    assert actual == data['files'], 'inventory or content mismatch'
    diagnostic = runpy.run_path(str(root / 'diagnostics.py'))['run']()
    assert diagnostic == json.loads((root / 'diagnostics.json').read_text()), 'diagnostic mismatch'
    return {'status': 'PASS', 'files': len(actual), 'anchor': anchor, 'scope': 'inventory and finite arithmetic only'}

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(args.root, args.anchor), sort_keys=True))
    except (AssertionError, OSError, ValueError, KeyError) as error:
        print(json.dumps({'status': 'FAIL', 'reason': str(error)}))
        raise SystemExit(1)
