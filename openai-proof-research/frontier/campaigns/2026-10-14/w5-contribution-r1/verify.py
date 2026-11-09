#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang. No affiliation.
# Original read-only verifier for the W5 contribution review r1.
# Usage: python3 -I verify.py --anchor <manifest sha256 supplied externally> [--repo REPO_ROOT]
import argparse, hashlib, json, subprocess, sys
from pathlib import Path, PurePosixPath

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
AUTHOR_ANCHOR = '10665dc832a51bca7651cbb091951b8b3ae3a7442339a64fd3b69e4b9743c606'
SCOPE = 'bda045b928a2f5b4ea52b96eb1ae6f3ea17146a575cefd955461994399d19f03'
CANDIDATE = '2fd9649ae04c531eca486848917cbc3dc7ddfffdac9881ff1742594d2060147d'

def sha(b): return hashlib.sha256(b).hexdigest()

def need(ok, msg):
    if not ok: raise ValueError(msg)

def safe(name):
    q = PurePosixPath(name)
    need(str(q) == name and not q.is_absolute() and '..' not in q.parts and name not in ('', '.'), 'unsafe path')
    return name

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--repo', type=Path, help='optional openai-proof-research root: re-check author packet bytes and run its verifier')
    a = ap.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'manifest.json').read_bytes()
    need(sha(raw) == a.anchor, 'external manifest anchor mismatch')
    m = json.loads(raw)
    need(m['schema'] == 'W5-contribution-r1-exact-v1', 'schema')
    need(m['verdict'] == 'TECHNICAL', 'verdict field')
    files = {safe(e['path']): e for e in m['files']}
    need(len(files) == len(m['files']) and 'manifest.json' not in files, 'duplicate/self entry')
    af, ad = set(), set()
    for p in root.rglob('*'):
        need(not p.is_symlink(), 'symlink present')
        n = p.relative_to(root).as_posix()
        if '__pycache__' in p.parts: need(False, 'cache directory present')
        (af if p.is_file() else ad).add(n)
    need(af == set(files) | {'manifest.json'}, 'exact file membership mismatch')
    need(ad == set(m['directories']), 'exact directory membership mismatch')
    for n, e in files.items():
        b = (root / n).read_bytes()
        need(len(b) == e['bytes'] and sha(b) == e['sha256'], 'payload mismatch: ' + n)
    ih = json.loads((root / 'input-hashes.json').read_text())
    need(ih['pin'] == PIN and ih['author_anchor'] == AUTHOR_ANCHOR and ih['scope_sha256'] == SCOPE
         and ih['candidate_sha256'] == CANDIDATE, 'reviewed identity mismatch')
    for e in ih['source_files']:
        b = (root / safe(e['path'])).read_bytes()
        g = hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()
        need(g == e['git_blob'] and sha(b) == e['sha256'], 'source bytes mismatch: ' + e['path'])
        need(e['url'] == 'https://raw.githubusercontent.com/openai/math/%s/%s' % (PIN, e['upstream_path']), 'url')
    for e in ih['primary_files']:
        b = (root / safe(e['path'])).read_bytes()
        need(sha(b) == e['sha256'], 'primary mismatch: ' + e['path'])
        if e['path'].endswith('.pdf'): need(b.startswith(b'%PDF'), 'mislabeled pdf')
    out = subprocess.run([sys.executable, '-I', str(root / 'coefficient_check.py')], capture_output=True, text=True)
    need(out.returncode == 0 and out.stdout.startswith('COEFFICIENT_IDENTITY_EXACT'), 'coefficient check failed')
    if a.repo:
        tree = json.loads((a.repo / 'sources/preprints-tree.json').read_text())
        need(tree['truncated'] is False, 'tree truncated')
        blobs = {t['path']: t['sha'] for t in tree['tree'] if t['type'] == 'blob'}
        for e in ih['source_files']:
            if e['upstream_path'].startswith('preprints/'):
                need(blobs.get(e['upstream_path']) == e['git_blob'], 'tree blob mismatch: ' + e['upstream_path'])
        for e in ih['author_files']:
            b = (a.repo / safe(e['path'])).read_bytes()
            need(sha(b) == e['sha256'], 'author packet changed: ' + e['path'])
    print(json.dumps({'status': 'REVIEW_IDENTITY_VERIFIED_NOT_PROOF', 'verdict': m['verdict'],
                      'payloads': len(files), 'source_files': len(ih['source_files']),
                      'primary_files': len(ih['primary_files']), 'author_anchor': AUTHOR_ANCHOR,
                      'manifest_sha256': a.anchor, 'repo_checks': bool(a.repo)}, sort_keys=True))

if __name__ == '__main__':
    try: main()
    except Exception as exc:
        print('VERIFICATION_FAILED: %s' % exc, file=sys.stderr); sys.exit(1)
