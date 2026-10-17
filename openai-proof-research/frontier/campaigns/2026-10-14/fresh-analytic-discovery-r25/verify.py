#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang. No affiliation.
# Original verifier for this W5 packet; no inherited helper source.
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SCOPE = 'bda045b928a2f5b4ea52b96eb1ae6f3ea17146a575cefd955461994399d19f03'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def need(ok, message):
    if not ok:
        raise ValueError(message)

def safe(name):
    q = PurePosixPath(name)
    need(isinstance(name, str) and str(q) == name and not q.is_absolute()
         and name not in ('', '.') and '..' not in q.parts, 'unsafe relative path')
    return name

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--repo', type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root/'manifest.json').read_bytes()
    need(digest(raw) == args.anchor, 'external manifest anchor mismatch')
    m = json.loads(raw)
    need(m['schema'] == 'W5-exact-membership-v1', 'manifest schema')
    expected = {safe(e['path']): e for e in m['files']}
    need(len(expected) == len(m['files']) and 'manifest.json' not in expected, 'duplicate/self payload')
    actual_files, actual_dirs = set(), set()
    for p in root.rglob('*'):
        need(not p.is_symlink(), 'symlink not allowed')
        name = p.relative_to(root).as_posix()
        if p.is_file(): actual_files.add(name)
        elif p.is_dir(): actual_dirs.add(name)
        else: need(False, 'nonregular payload')
    need(actual_files == set(expected) | {'manifest.json'}, 'exact file membership mismatch')
    need(actual_dirs == set(m['directories']), 'exact directory membership mismatch')
    for name, e in expected.items():
        b = (root/name).read_bytes()
        need(len(b) == e['bytes'] and digest(b) == e['sha256'], 'payload mismatch: '+name)
    scope = (root/'original-scope.md').read_bytes()
    need(digest(scope) == SCOPE, 'original full scope mismatch')
    fr = json.loads((root/'freeze-receipt.json').read_text())
    need(fr['scope_sha256'] == SCOPE, 'freeze scope mismatch')
    for name, h in fr['pre_freeze_files'].items():
        need(digest((root/safe(name)).read_bytes()) == h, 'pre-freeze receipt mismatch')
    ir = json.loads((root/'input-receipt.json').read_text())
    for e in ir['entries']:
        b = (root/safe(e['copy'])).read_bytes()
        need(len(b) == e['bytes'] and digest(b) == e['sha256'], 'context input mismatch')
        if args.repo:
            need(digest((args.repo/safe(e['repo_path'])).read_bytes()) == e['sha256'],
                 'original historical context changed: '+e['repo_path'])
    tree = json.loads((root/'inputs/sources/preprints-tree.json').read_text())
    need(tree['truncated'] is False, 'complete tree required')
    blobs = {e['path']:e['sha'] for e in tree['tree'] if e['type'] == 'blob'}
    sr = json.loads((root/'source-receipt.json').read_text())
    need(sr['pin'] == PIN, 'pin mismatch')
    for e in sr['entries']:
        b = (root/safe(e['path'])).read_bytes()
        gh = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        need(gh == e['git_blob'] == blobs[e['upstream_path']], 'pinned Git blob mismatch')
        need(digest(b) == e['sha256'] and len(b) == e['bytes'], 'pinned SHA256 mismatch')
        need(e['url'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['upstream_path'],
             'source URL mismatch')
    pr = json.loads((root/'primary-receipt.json').read_text())
    retained = [e for e in pr if 'file' in e]
    for e in retained:
        b = (root/safe(e['file'])).read_bytes()
        need(len(b) == e['size'] and digest(b) == e['sha256'], 'primary receipt mismatch')
        if e['file'].endswith('.pdf'): need(b.startswith(b'%PDF'), 'non-PDF mislabeled')
    print(json.dumps({'status':'IDENTITY_VERIFIED_NOT_MATHEMATICAL_VERDICT',
        'payloads':len(expected), 'context_inputs':len(ir['entries']),
        'pinned_blobs':len(sr['entries']), 'retained_primary_files':len(retained),
        'scope_sha256':SCOPE, 'manifest_sha256':args.anchor}, sort_keys=True))

if __name__ == '__main__':
    try: main()
    except Exception as exc:
        print('VERIFICATION_FAILED: '+str(exc), file=sys.stderr)
        sys.exit(1)
