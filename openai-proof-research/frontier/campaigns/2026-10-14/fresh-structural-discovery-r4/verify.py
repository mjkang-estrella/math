#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT licensed; see RIGHTS.md.
"""Authenticate immutable evidence before zero-write finite-check replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
SPECIAL = {'input-manifest.json', 'output-manifest.json', 'seal.json'}


def fail(msg):
    raise RuntimeError(msg)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def path_of(name):
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or not p.parts or str(p) != name:
        fail('unsafe inventory path: '+repr(name))
    q = ROOT.joinpath(*p.parts)
    if not q.is_file() or any(x.is_symlink() for x in (q, *q.parents)):
        fail('missing file or symlink: '+name)
    return q


def authenticate(seal_hash):
    seal_bytes = (ROOT/'seal.json').read_bytes()
    if digest(seal_bytes) != seal_hash:
        fail('seal SHA256 mismatch')
    seal = json.loads(seal_bytes)
    if seal.get('schema') != 'r4-seal-v1':
        fail('unknown seal schema')
    records = []
    for name in ('input-manifest.json', 'output-manifest.json'):
        b = (ROOT/name).read_bytes()
        expected = seal['inventories'][name]
        if len(b) != expected['size'] or digest(b) != expected['sha256']:
            fail('inventory authentication failed: '+name)
        inv = json.loads(b)
        if inv.get('schema') != 'r4-inventory-v1':
            fail('unknown inventory schema')
        records.extend(inv['files'])
    names = [r['path'] for r in records]
    if len(names) != len(set(names)) or set(names) & SPECIAL:
        fail('duplicate or reserved inventory path')
    actual = set()
    for p in ROOT.rglob('*'):
        if p.is_symlink():
            fail('symlink in package: '+str(p.relative_to(ROOT)))
        if p.is_file():
            actual.add(p.relative_to(ROOT).as_posix())
    if actual != set(names) | SPECIAL:
        fail('exact membership mismatch')
    for record in records:
        b = path_of(record['path']).read_bytes()
        if len(b) != record['size'] or digest(b) != record['sha256']:
            fail('file authentication failed: '+record['path'])
    pinned = json.loads((ROOT/'retrieval-pinned.json').read_text())
    tree = json.loads((ROOT/'inputs/private/context/sources/preprints-tree.json').read_text())
    if tree['truncated']:
        fail('truncated preprint tree')
    blobs = {p['path']: p['sha'] for p in tree['tree'] if p['type'] == 'blob'}
    for record in pinned:
        b = path_of(record['path']).read_bytes()
        rel = str(PurePosixPath(record['path']).relative_to('inputs/private/pinned'))
        git_sha = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if git_sha != record['git_blob'] or git_sha != blobs[rel]:
            fail('pinned Git blob mismatch: '+rel)
        if len(b) != record['size'] or digest(b) != record['sha256']:
            fail('retrieval binding mismatch: '+rel)
        if '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' not in record['url']:
            fail('unpinned URL')
    return len(records), len(pinned)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seal-sha256', required=True)
    args = parser.parse_args()
    if len(args.seal_sha256) != 64 or any(c not in '0123456789abcdef' for c in args.seal_sha256):
        fail('expected a lowercase SHA256 from the handoff')
    count, blobs = authenticate(args.seal_sha256)
    # Both the stored receipt and executable have already been authenticated.
    expected = (ROOT/'checks-receipt.json').read_bytes()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    replay = subprocess.run([sys.executable, '-B', str(ROOT/'checks.py')],
                            cwd=ROOT, env=env, capture_output=True, timeout=120)
    if replay.returncode or replay.stderr:
        fail('finite replay failed: '+replay.stderr.decode(errors='replace')[:500])
    if replay.stdout != expected:
        fail('authenticated receipt replay differs')
    if authenticate(args.seal_sha256) != (count, blobs):
        fail('package changed during replay')
    print(json.dumps({'status': 'PASS_integrity_and_finite_support_only',
                      'authenticated_files': count, 'pinned_blobs': blobs,
                      'receipt_sha256': digest(expected), 'writes': 0,
                      'network': False, 'target_T2': 'UNRESOLVED'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('VERIFY FAILED: '+str(exc), file=sys.stderr)
        sys.exit(1)
