#!/usr/bin/env python3
"""MIT. Read-only exact-byte receipt verifier; not a mathematical certificate."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def digest(b):
    return hashlib.sha256(b).hexdigest()

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

p = argparse.ArgumentParser()
p.add_argument('--anchor', required=True)
a = p.parse_args()
root = Path(__file__).resolve().parent
try:
    raw = (root / 'manifest.json').read_bytes()
    require(digest(raw) == a.anchor, 'manifest anchor mismatch')
    manifest = json.loads(raw)
    expected = {}
    for entry in manifest['files']:
        name = entry['path']
        q = PurePosixPath(name)
        require(str(q) == name and not q.is_absolute() and '..' not in q.parts,
                'noncanonical path')
        require(name not in expected and name != 'manifest.json', 'duplicate/reserved path')
        expected[name] = entry
    actual = set()
    dirs = set()
    for f in root.rglob('*'):
        require(not f.is_symlink(), 'symlink')
        rel = f.relative_to(root).as_posix()
        if f.is_dir():
            dirs.add(rel)
        else:
            require(f.is_file(), 'special file')
            if rel != 'manifest.json':
                actual.add(rel)
    require(actual == set(expected), 'file membership mismatch')
    require(dirs == set(manifest['directories']), 'directory membership mismatch')
    for name, entry in expected.items():
        b = (root / name).read_bytes()
        require(len(b) == entry['bytes'] and digest(b) == entry['sha256'], name)
    src = json.loads((root / 'source-receipt.json').read_text())
    for entry in src['sources']:
        b = (root / entry['local']).read_bytes()
        git = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(git == entry['git_blob'] and digest(b) == entry['sha256'], 'pinned blob')
    prim = json.loads((root / 'private/primary-receipt.json').read_text())
    for entry in prim:
        b = (root / 'private' / entry['file']).read_bytes()
        require(len(b) == entry['bytes'] and digest(b) == entry['sha256'], 'primary PDF')
    print(json.dumps({'result':'INTEGRITY_ONLY','payloads':len(expected),
                      'pinned_blobs':len(src['sources']),'primary_pdfs':len(prim),
                      'external_contexts_bound':False,'writes':0,'counted':False}))
except (ValueError, KeyError, OSError, TypeError) as exc:
    raise SystemExit('REJECT: ' + str(exc))
