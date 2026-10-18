#!/usr/bin/env python3
"""Read-only integrity check for the T298P contribution review r1. Not mathematics.

Adapted from the t224g-contribution-r1/verify.py pattern (same campaign), with
explicit rejection of symlinks/non-regular entries and an optional author-packet
anchor check. Reads bytes only; never writes.
"""
import argparse, hashlib, json, sys
from pathlib import Path

VERDICT = 'SUBSTANTIAL'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def verify(root, anchor, author=None):
    root = Path(root)
    raw = (root/'MANIFEST.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != anchor: raise ValueError('external manifest anchor mismatch')
    m = json.loads(raw)
    if m.get('verdict') != VERDICT or m.get('counts') != 0 or m.get('accepts') is not False:
        raise ValueError('verdict/count fields altered')
    entries = [p for p in root.rglob('*') if '__pycache__' not in p.parts]
    for p in entries:
        if p.is_symlink() or not (p.is_file() or p.is_dir()): raise ValueError('non-regular entry: '+str(p.relative_to(root)))
        if p.is_dir(): raise ValueError('unexpected subdirectory: '+str(p.relative_to(root)))
    actual = {str(p.relative_to(root)) for p in entries if p.name != 'MANIFEST.json'}
    if actual != set(m['files']): raise ValueError('inventory mismatch')
    for n, h in m['files'].items():
        if Path(n).is_absolute() or '..' in Path(n).parts: raise ValueError('unsafe manifest path: '+n)
        if sha(root/n) != h: raise ValueError('payload hash mismatch: '+n)
    if author:
        for n, h in m['author_anchors'].items():
            if sha(Path(author)/n) != h: raise ValueError('author anchor mismatch: '+n)
    return {'status': 'PASS_INTEGRITY_ONLY', 'files': len(m['files']), 'verdict_field': m['verdict'],
            'author_anchors_checked': bool(author), 'scope': 'identity only; not a mathematical or acceptance verdict'}

if __name__ == '__main__':
    a = argparse.ArgumentParser()
    a.add_argument('--root', default=str(Path(__file__).resolve().parent))
    a.add_argument('--manifest-sha256', required=True)
    a.add_argument('--author-packet')
    x = a.parse_args()
    try: print(json.dumps(verify(x.root, x.manifest_sha256, x.author_packet)))
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as e: sys.exit('REJECT: '+str(e))
