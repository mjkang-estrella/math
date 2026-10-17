#!/usr/bin/env python3
# Original code MIT. Read-only integrity verifier; no mathematical claims.
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

base = Path(__file__).resolve().parent

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    p = PurePosixPath(name)
    assert name and not p.is_absolute() and str(p) == name
    assert all(x not in ('', '.', '..') for x in p.parts)
    return name

assert len(sys.argv) == 2, 'external seal SHA256 required'
seal_path = base / 'seal.json'
assert not seal_path.is_symlink()
raw = seal_path.read_bytes()
assert digest(raw) == sys.argv[1], 'seal anchor mismatch'
seal = json.loads(raw)
manifest_path = base / 'manifest.json'
assert not manifest_path.is_symlink()
raw = manifest_path.read_bytes()
assert digest(raw) == seal['manifest_sha256'], 'manifest mismatch'
m = json.loads(raw)
expected = {'seal.json', 'manifest.json'}
for item in m['files']:
    name = safe(item['path'])
    assert name not in expected, 'duplicate/reserved path'
    expected.add(name)
    p = base / name
    assert p.is_file() and not p.is_symlink()
    b = p.read_bytes()
    assert len(b) == item['bytes'] and digest(b) == item['sha256'], name
actual = set()
dirs = set()
for p in base.rglob('*'):
    assert not p.is_symlink(), 'symlink'
    name = p.relative_to(base).as_posix()
    if p.is_dir():
        dirs.add(name)
    else:
        actual.add(name)
assert actual == expected, 'membership mismatch'
assert dirs == set(m['directories']), 'directory mismatch'
status = json.loads((base/'status.json').read_bytes())
assert status['verdict'] == 'TECHNICAL' and status['counted'] is False
assert status['scope_unchanged'] is True
assert status['proof_verdict'] == 'NOT_AWARDED_BY_THIS_REVIEW'
assert digest((base/'candidate.md').read_bytes()) == status['candidate_sha256']
assert digest((base/'original-scope.md').read_bytes()) == status['scope_sha256']
print('PASS: exact review membership, hashes, scope and contribution metadata; no mathematical certification')
