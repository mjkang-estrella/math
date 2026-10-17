#!/usr/bin/env python3
"""Original review verifier, MIT. Offline/read-only; no mathematical programs."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

def digest(b):
    return hashlib.sha256(b).hexdigest()

def unique_pairs(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError('duplicate JSON key')
        out[k] = v
    return out

def parse(b):
    return json.loads(b, object_pairs_hook=unique_pairs)

def safe(s):
    p = PurePosixPath(s)
    if not s or p.is_absolute() or '..' in p.parts or str(p) != s:
        raise ValueError('noncanonical path')

def verify(root, anchor):
    if not re.fullmatch('[0-9a-f]{64}', anchor):
        raise ValueError('invalid external anchor')
    if root.is_symlink() or not root.is_dir():
        raise ValueError('unsafe root')
    mf = root / 'manifest.json'
    if mf.is_symlink() or not mf.is_file():
        raise ValueError('unsafe manifest')
    raw = mf.read_bytes()
    if digest(raw) != anchor:
        raise ValueError('external anchor mismatch')
    inv = parse(raw)
    actual, dirs = {}, []
    for p in sorted(root.rglob('*')):
        if p.is_symlink():
            raise ValueError('symlink forbidden')
        name = p.relative_to(root).as_posix()
        safe(name)
        if '__pycache__' in p.parts or p.suffix == '.pyc':
            raise ValueError('bytecode forbidden')
        if p.is_dir():
            dirs.append(name)
        elif p.is_file():
            if name != 'manifest.json':
                b = p.read_bytes()
                actual[name] = {'bytes': len(b), 'sha256': digest(b)}
        else:
            raise ValueError('special file forbidden')
    if actual != inv['files'] or dirs != inv['directories']:
        raise ValueError('exact inventory mismatch')
    for name in inv['files']:
        safe(name)
    def read(name):
        safe(name)
        if name not in actual:
            raise ValueError('unlisted input')
        return (root / name).read_bytes()
    receipts = parse(read('input-receipts.json'))
    for r in receipts['snapshots']:
        b = read(r['snapshot'])
        if len(b) != r['bytes'] or digest(b) != r['sha256']:
            raise ValueError('input snapshot mismatch')
    if digest(read('private/author/output-manifest.json')) != receipts['author_anchor']:
        raise ValueError('author anchor mismatch')
    expected_scope = 'cfb52e908976e2968bda9404e615cca27ad9c9b7ea5b19b78fb2885b8d22810b'
    expected_candidate = '2f550b13bee014b9b40657b15c06a4fb112b4b732327ee4bd101662d47adbc87'
    if digest(read('private/author/original-scope.md')) != expected_scope or digest(read('private/author/candidate.md')) != expected_candidate:
        raise ValueError('scope/candidate mismatch')
    tree = {r['path']: r['sha'] for r in receipts['matched_selected_records']}
    sources = parse(read('private/author/source-receipt.json'))
    copied = 0
    for r in sources:
        path = r['path']
        if tree.get(path, tree.get(path.removeprefix('preprints/'))) != r['git_blob']:
            raise ValueError('selected tree mismatch')
        rel = 'private/source/' + PurePosixPath(r['local']).name
        if rel in actual:
            b = read(rel)
            blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            if blob != r['git_blob'] or digest(b) != r['sha256'] or len(b) != r['bytes']:
                raise ValueError('copied pinned source mismatch')
            copied += 1
    for r in parse(read('private/primary/receipts.json')):
        b = read('private/primary/' + r['name'] + '.pdf')
        if not b.startswith(b'%PDF') or len(b) != r['bytes'] or digest(b) != r['sha256']:
            raise ValueError('primary PDF mismatch')
    return {'status': 'IDENTITY_ONLY', 'files': len(actual), 'directories': len(dirs),
            'author_source_tree_matches': len(sources), 'copied_pinned_sources': copied,
            'primary_pdfs': 5, 'mathematical_programs_executed': False,
            'verifier_is_not_a_proof': True}

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--anchor', required=True)
    args = p.parse_args()
    try:
        print(json.dumps(verify(Path(__file__).parent, args.anchor), sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError) as exc:
        p.exit(1, 'VERIFY_REJECTED: ' + str(exc) + '\n')

if __name__ == '__main__':
    main()
