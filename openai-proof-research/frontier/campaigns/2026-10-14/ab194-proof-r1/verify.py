#!/usr/bin/env python3
"""MIT License. Myeongjin Kang. Read-only exact-byte verifier for the AB194
proof-r1 review packet; also rechecks the reviewed author bytes. Integrity
only: this is not a mathematical certificate."""
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
        need(str(q) == e['path'] and not q.is_absolute() and '..' not in q.parts, 'noncanonical path')
        need(e['path'] not in exp and e['path'] != 'manifest.json', 'duplicate/reserved')
        exp[e['path']] = e
    act, dirs = set(), set()
    for f in root.rglob('*'):
        need(not f.is_symlink(), 'symlink')
        rel = f.relative_to(root).as_posix()
        if rel.startswith('__pycache__'): continue
        if f.is_dir(): dirs.add(rel)
        elif rel != 'manifest.json': act.add(rel)
    need(act == set(exp), 'file membership mismatch')
    need(dirs == set(m['directories']), 'directory membership mismatch')
    for n, e in exp.items():
        b = (root / n).read_bytes()
        need(len(b) == e['bytes'] and sha(b) == e['sha256'], n)
    rh = json.loads((root / 'reviewed-hashes.json').read_text())
    need(rh['verdict'] == m['verdict'] == 'PASS_FULL_AB194', 'verdict')
    need(rh['reviewed_scope_sha256'] == m['reviewed_scope_sha256'], 'scope binding')
    need(rh['reviewed_proof_sha256'] == m['reviewed_proof_sha256'], 'proof binding')
    checked = 0
    for e in rh['reviewed_files']:
        p = repo / e['path']
        if p.exists():
            b = p.read_bytes()
            need(len(b) == e['bytes'] and sha(b) == e['sha256'], 'author bytes ' + e['path'])
            checked += 1
    print(json.dumps({'result': 'INTEGRITY_ONLY', 'payloads': len(exp),
                      'author_files_rechecked': checked,
                      'author_files_listed': len(rh['reviewed_files']),
                      'verdict_recorded': rh['verdict'], 'writes': 0}))
except (ValueError, KeyError, OSError, TypeError) as exc:
    raise SystemExit('REJECT: ' + str(exc))
