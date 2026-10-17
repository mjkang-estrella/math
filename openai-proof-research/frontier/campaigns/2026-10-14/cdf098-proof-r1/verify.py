#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only exact-byte verifier for the CDF098 proof-r1 review packet.
It also rechecks the reviewed author bytes. This is an integrity check only,
not a mathematical certificate. It does not execute checks/."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def sha(b): return hashlib.sha256(b).hexdigest()
def need(ok, why):
    if not ok: raise ValueError(why)

ap = argparse.ArgumentParser(); ap.add_argument('--anchor', required=True)
a = ap.parse_args()
root = Path(__file__).resolve().parent
repo = root.parents[3]  # .../openai-proof-research
try:
    raw = (root / 'manifest.json').read_bytes()
    need(sha(raw) == a.anchor, 'manifest anchor mismatch')
    m = json.loads(raw)
    exp = {}
    for e in m['files']:
        q = PurePosixPath(e['path'])
        need(q.as_posix() == e['path'] and not q.is_absolute() and '..' not in q.parts, 'noncanonical path')
        need(e['path'] not in exp and e['path'] != 'manifest.json', 'duplicate/reserved')
        exp[e['path']] = e
    act, dirs = set(), set()
    for f in root.rglob('*'):
        need(not f.is_symlink(), 'symlink')
        rel = f.relative_to(root).as_posix()
        if f.is_dir(): dirs.add(rel)
        elif f.is_file():
            if rel != 'manifest.json': act.add(rel)
        else: raise ValueError('special file')
    need(act == set(exp), 'file membership mismatch')
    need(dirs == set(m['directories']), 'directory membership mismatch')
    for n, e in exp.items():
        b = (root / n).read_bytes()
        need(len(b) == e['bytes'] and sha(b) == e['sha256'], n)
    rh = json.loads((root / 'reviewed-hashes.json').read_text())
    need(rh['verdict'] == m['verdict'] == 'PASS_FULL_CDF098', 'verdict')
    for k in ('author_manifest_sha256', 'reviewed_scope_sha256', 'reviewed_proof_sha256'):
        need(rh[k] == m[k], 'binding ' + k)
    checked = 0
    for e in rh['reviewed_files']:
        b = (repo / e['path']).read_bytes()
        need(len(b) == e['bytes'] and sha(b) == e['sha256'], 'reviewed bytes ' + e['path'])
        checked += 1
    by = {e['path'].rsplit('/', 1)[-1]: e['sha256'] for e in rh['reviewed_files']}
    need(by['manifest.json'] == rh['author_manifest_sha256'] and by['original-scope.md'] == rh['reviewed_scope_sha256']
         and by['candidate.md'] == rh['reviewed_proof_sha256'], 'reviewed identity')
    print(json.dumps({'result': 'INTEGRITY_ONLY', 'payloads': len(exp),
                      'reviewed_files_rechecked': checked,
                      'verdict_recorded': rh['verdict'], 'mathematical_code_executed': False,
                      'writes': 0, 'count_changed': False}))
except (ValueError, KeyError, OSError, TypeError) as exc:
    raise SystemExit('REJECT: ' + str(exc))
