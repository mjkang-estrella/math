#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only integrity checks; no experiments, mathematical gate, or live ledger.

An external seal anchor is mandatory. Negative controls change an in-memory
file view only. Scope/status controls reseal that view to test semantic gates
in addition to ordinary hash detection. This script never writes a file.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SCOPE = 'd14eb78f156fda839a910797953d27445492625839dd6d0e2d22a2059fda29b4'
AUTHOR = '4a57c056b08c74d48fd78bd4152e3eb0bfddefe83adbd0c03e98fdd53c6786e8'
REVISION = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
BLOBS = {
    'README.md': '575cccc262d3d9c9e7a87df235884857a1620f79',
    'main.tex': '676dc958b88fa0062b3949895c4b01092a9bab64',
    'references.bib': 'ef5e68b8d708d1a263e6db20f873a76bfba5776b',
    'sections/cells.tex': '15cf607375c84a422c8aa4b69c9b2791651fd13c',
    'sections/finite_stability.tex': 'ebb83b10ad60efd546708576f5a6fd339a8eb90e',
    'sections/gradient.tex': 'baebc01672a5e6e1e83838192e4fb3a56ab201b6',
    'sections/introduction.tex': 'a3f79cd0ba261e054ad3ebb0a5641453788f20ef',
    'sections/moments.tex': 'b1645cc9b0cf7982c28ba13b1138b86cbd664b2c',
    'sections/sharpness.tex': 'ae214b7d19cd630fccf6da61b4e169fd329b28e8',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def safe(name):
    p = PurePosixPath(name)
    require(bool(name) and not p.is_absolute() and '..' not in p.parts
            and str(p) == name, 'unsafe manifest path')


def verify(anchor, overlay=None, extra=None):
    overlay = overlay or {}
    read = lambda name: overlay[name] if name in overlay else (HERE / name).read_bytes()
    # Fail before interpreting manifests or examining author originals.
    require(digest(read('seal.json')) == anchor, 'external review seal anchor mismatch')
    s = json.loads(read('seal.json'))
    require(s['format'] == 'lc-review-r1-seal-v1', 'seal format')
    require(s['scope_sha256'] == SCOPE and s['author_seal_sha256'] == AUTHOR,
            'immutable source/scope anchor metadata')
    require(s['mathematical_verdict'] == 'PASS_FULL_LC'
            and s['contribution_verdict'] == 'TECHNICAL'
            and s['counted'] is False, 'seal verdict/count metadata')
    require(read('seal.sha256').decode().strip() == anchor + '  seal.json',
            'detached review seal mismatch')
    names = set()
    for kind in ('inputs', 'outputs'):
        name = kind + '-manifest.json'
        entry = s[kind]
        require(entry['path'] == name, 'manifest name')
        b = read(name)
        require(len(b) == entry['size'] and digest(b) == entry['sha256'],
                'manifest hash: ' + name)
        manifest = json.loads(b)
        require(manifest['format'] == 'sha256-size-v1', 'payload manifest format')
        for r in manifest['files']:
            path = r['path']
            safe(path)
            require(path not in names, 'duplicate payload member: ' + path)
            require(path.startswith('inputs/') == (kind == 'inputs'),
                    'input/output classification: ' + path)
            names.add(path)
            b = read(path)
            require(len(b) == r['size'] and digest(b) == r['sha256'],
                    'payload hash: ' + path)
    inventory = list(HERE.rglob('*'))
    require(not any(p.is_symlink() for p in inventory), 'symlink in review package')
    present = {p.relative_to(HERE).as_posix() for p in inventory if p.is_file()}
    present |= set(extra or ())
    expected = names | {'inputs-manifest.json', 'outputs-manifest.json', 'seal.json', 'seal.sha256'}
    require(present == expected, 'exact review file membership')
    directories = {p.relative_to(HERE).as_posix() for p in inventory if p.is_dir()}
    require(directories == set(s['directories']), 'exact review directory membership')
    require(digest(read('inputs/author/original-scope.md')) == SCOPE,
            'frozen scope hash')
    status = json.loads(read('status.json'))
    require(status['mathematical_verdict'] == 'PASS_FULL_LC'
            and status['contribution_verdict'] == 'TECHNICAL'
            and status['counted'] is False and status['campaign_count'] == 4
            and status['publication_authorized'] is False
            and status['original_proof_repaired'] is False, 'status verdict/count gate')
    require(status['scope_sha256'] == SCOPE and status['author_seal_sha256'] == AUTHOR
            and status['upstream_revision'] == REVISION, 'status immutable scope/source')
    cat = json.loads(read('inputs/context/sources/preprints-tree.json'))
    require(not cat.get('truncated', False), 'complete pinned catalogue')
    table = {r['path']: r for r in cat['tree']}
    base = 'preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/'
    for name, expected_blob in BLOBS.items():
        b = read('inputs/author/inputs/pinned/brenier/' + name)
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        path = base + ('' if name == 'README.md' else 'build/source/') + name
        require(blob == expected_blob == table[path]['sha'], 'pinned Git blob: ' + name)
    require(digest(read('inputs/author/seal.json')) == AUTHOR, 'author seal anchor')
    before = json.loads(read('inputs/author-before.json'))
    require(before['anchor'] == AUTHOR and len(before['files']) == 33,
            'original author receipt metadata')
    original = HERE.parent / 'fresh-analytic-discovery-r12'
    original_paths = list(original.rglob('*'))
    require(not any(p.is_symlink() for p in original_paths), 'symlink in author original')
    actual = {p.relative_to(original).as_posix() for p in original_paths if p.is_file()}
    frozen = {r['path'] for r in before['files']}
    require(actual == frozen, 'exact unchanged author membership')
    for r in before['files']:
        safe(r['path'])
        b = (original / r['path']).read_bytes()
        require(len(b) == r['size'] and digest(b) == r['sha256'],
                'author original changed: ' + r['path'])
        require(read('inputs/author/' + r['path']) == b,
                'author snapshot mismatch: ' + r['path'])
    return {'ok': True, 'owned_files': len(present), 'owned_directories': len(directories),
            'author_originals': 33, 'pinned_blobs': 9,
            'meaning': 'integrity only; no mathematical formalization or numerical replay'}


def negative_view(anchor, kind):
    # Authenticate the real view first. No control can hide an existing failure.
    verify(anchor)
    if kind == 'extra-member':
        return anchor, {}, {'UNLISTED-CONTROL.txt'}
    path = 'inputs/author/original-scope.md' if kind == 'scope-byte' else 'status.json'
    b = (HERE / path).read_bytes()
    if kind == 'scope-byte':
        b += b'\nCONTROL: altered frozen scope\n'
    else:
        v = json.loads(b)
        v['counted'] = True
        v['contribution_verdict'] = 'SUBSTANTIAL'
        b = encode(v)
    manifest_name = 'inputs-manifest.json' if path.startswith('inputs/') else 'outputs-manifest.json'
    m = json.loads((HERE / manifest_name).read_bytes())
    for r in m['files']:
        if r['path'] == path:
            r.update(size=len(b), sha256=digest(b))
    mb = encode(m)
    seal = json.loads((HERE / 'seal.json').read_bytes())
    key = 'inputs' if path.startswith('inputs/') else 'outputs'
    seal[key].update(size=len(mb), sha256=digest(mb))
    sb = encode(seal)
    new_anchor = digest(sb)
    return new_anchor, {path: b, manifest_name: mb, 'seal.json': sb,
                        'seal.sha256': (new_anchor + '  seal.json\n').encode()}, set()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--negative-control', choices=('scope-byte', 'extra-member', 'counterfeit-status'))
    args = ap.parse_args()
    try:
        anchor, overlay, extra = args.anchor, {}, set()
        if args.negative_control:
            anchor, overlay, extra = negative_view(anchor, args.negative_control)
        result = verify(anchor, overlay, extra)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print(json.dumps({'ok': False, 'error': str(exc)}, sort_keys=True))
        return 1


if __name__ == '__main__':
    sys.exit(main())
