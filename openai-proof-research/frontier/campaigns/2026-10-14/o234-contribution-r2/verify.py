#!/usr/bin/env python3
# Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
# Read-only verifier for o234-contribution-r2: no network, subprocess, writes or resealing.
# Requires the EXTERNAL expected SHA256 of manifest.json; identity only, never a verdict.
import argparse, hashlib, json, re
from pathlib import Path, PurePosixPath

UNLISTED = {'manifest.json', 'seal-receipt.json'}

def sha(b): return hashlib.sha256(b).hexdigest()

def verify(root, anchor):
    if not re.fullmatch('[0-9a-f]{64}', anchor): raise ValueError('invalid external anchor')
    if root.is_symlink() or not root.is_dir(): raise ValueError('unsafe root')
    m = root / 'manifest.json'
    if m.is_symlink() or not m.is_file(): raise ValueError('missing regular manifest')
    raw = m.read_bytes()
    if sha(raw) != anchor: raise ValueError('external anchor mismatch')
    data = json.loads(raw)
    files, dirs = {}, set()
    for q in root.rglob('*'):
        if q.is_symlink(): raise ValueError('symlink forbidden')
        name = q.relative_to(root).as_posix()
        if q.is_dir(): dirs.add(name)
        elif q.is_file():
            if name not in UNLISTED: files[name] = q
        else: raise ValueError('special file forbidden')
    exp = data['files']
    if list(exp) != sorted(exp): raise ValueError('unsorted inventory')
    if set(files) != set(exp) or dirs != set(data['directories']):
        raise ValueError('exact membership mismatch')
    for name, rec in exp.items():
        p = PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts: raise ValueError('unsafe path')
        b = files[name].read_bytes()
        if len(b) != rec['bytes'] or sha(b) != rec['sha256']:
            raise ValueError('payload mismatch: ' + name)
    for k in ('author_manifest_sha256', 'author_candidate_sha256', 'author_scope_sha256'):
        if not re.fullmatch('[0-9a-f]{64}', data['bound'][k]): raise ValueError('bad bound anchor')
    return {'status': 'IDENTITY_ONLY', 'payloads': len(files), 'directories': len(dirs),
            'verdict_recorded': data['verdict'], 'bound': data['bound'],
            'mathematical_or_contribution_certificate': False}

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    a = ap.parse_args()
    try: print(json.dumps(verify(a.root, a.anchor), indent=2, sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as e:
        ap.exit(1, 'VERIFY_REJECTED: ' + str(e) + '\n')

if __name__ == '__main__': main()
