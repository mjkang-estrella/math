#!/usr/bin/env python3
# Original review verifier: Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only exact review inventory and anchored author-input verification."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

AUTHOR_ANCHOR = '1d299a1840795fe279f89aa04fd4ca55cb58d283b3f7ed2fb5001c136d97d48f'
CANDIDATE = 'a2aca38071a48fba5cccad7df731626202c6a8ca778ade57f76759c1d321cf37'
SCOPE = '78fc15d24a91bbc2a8e27f679b78c4e551ef0c25d84214dd5dcc48e14ee99584'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'manifest.json').read_bytes()
    require(sha(raw) == args.anchor, 'external review anchor mismatch')
    m = json.loads(raw)
    require(m['verdict'] == 'PASS_FULL_O217', 'review verdict label mismatch')
    paths = list(root.rglob('*'))
    require(not any(p.is_symlink() for p in paths), 'review symlink')
    files = {str(p.relative_to(root)): sha(p.read_bytes()) for p in paths if p.is_file() and p != root / 'manifest.json'}
    dirs = sorted(str(p.relative_to(root)) for p in paths if p.is_dir())
    require(files == m['files'] and dirs == m['directories'], 'exact review membership or hash mismatch')
    author = root.parent / 'fresh-analytic-discovery-r28'
    for name, expected in [('output-manifest.json', AUTHOR_ANCHOR), ('candidate.md', CANDIDATE), ('original-scope.md', SCOPE)]:
        require(sha((author / name).read_bytes()) == expected, 'author anchor mismatch: ' + name)
    repo = root.parents[3]
    reads = json.loads((root / 'input-read-receipts.json').read_text())
    for r in reads:
        rel = Path(r['path'])
        require(not rel.is_absolute() and '..' not in rel.parts, 'invalid recorded input path')
        b = (repo / rel).read_bytes()
        require(sha(b) == r['sha256'] and len(b) == r['bytes'], 'read input changed: ' + r['path'])
    tree = json.loads((repo / 'sources/preprints-tree.json').read_text())
    require(not tree.get('truncated', False) and len(tree['tree']) == 13223, 'incomplete source tree')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    sources = json.loads((author / 'source-receipts.json').read_text())
    require(len(sources) == 58, 'source count mismatch')
    for r in sources:
        b = (author / r['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(blob == r['git_blob'] == blobs.get(r['path']), 'current pinned blob mismatch')
    p = subprocess.run([sys.executable, '-B', str(author / 'verify.py'), '--anchor', AUTHOR_ANCHOR], capture_output=True, text=True)
    require(p.returncode == 0, 'anchored author verifier rejected: ' + p.stderr)
    result = json.loads(p.stdout)
    require(result['payloads'] == 111 and result['pinned_source_blobs'] == 58 and result['primary_pdfs'] == 8, 'author replay count mismatch')
    print(json.dumps({'status': 'REVIEW_INTEGRITY_OK', 'review_payloads': len(files), 'review_directories': len(dirs), 'read_input_hashes': len(reads), 'author_payloads': result['payloads'], 'pinned_blobs': len(sources), 'primary_pdfs': result['primary_pdfs'], 'recorded_verdict': m['verdict'], 'note': 'Integrity replay does not independently prove mathematics.'}, indent=2))

if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('REJECT: ' + str(e), file=sys.stderr)
        sys.exit(1)
