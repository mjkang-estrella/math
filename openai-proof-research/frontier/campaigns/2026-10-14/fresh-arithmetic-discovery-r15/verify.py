#!/usr/bin/env python3
"""Check a discovery packet against caller-supplied external anchors."""
import argparse
import hashlib
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--manifest-sha256', required=True)
p.add_argument('--checkpoint-sha256', required=True)
a = p.parse_args()
r = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha((r/'manifest.json').read_bytes()) == a.manifest_sha256, 'wrong external manifest anchor'
assert sha((r/'checkpoint.md').read_bytes()) == a.checkpoint_sha256, 'wrong external checkpoint anchor'
inventory = json.loads((r/'manifest.json').read_text())
actual = {str(f.relative_to(r)) for f in r.rglob('*') if f.is_file() and f.name != 'manifest.json'}
assert actual == set(inventory), 'inventory membership mismatch'
for local, digest in inventory.items():
    assert sha((r/local).read_bytes()) == digest, local
repo = r.parents[3]
tree = json.loads((repo/'sources/preprints-tree.json').read_text())['tree']
blobs = {e['path']: e['sha'] for e in tree if e['type'] == 'blob'}
pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
for receipt in json.loads((r/'receipts.json').read_text()):
    b = (r/receipt['local']).read_bytes()
    git = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert git == blobs[receipt['path']] == receipt.get('git_sha1', receipt.get('sha1'))
    assert sha(b) == receipt['sha256']
    assert receipt['url'] == f'https://raw.githubusercontent.com/openai/math/{pin}/'+receipt['path']
for receipt in json.loads((r/'primary-receipts.json').read_text()):
    assert sha((r/receipt['local']).read_bytes()) == receipt['sha256']
print('PASS: external anchors, exact inventory, source-pin blobs, primary hashes. No proof verdict.')
