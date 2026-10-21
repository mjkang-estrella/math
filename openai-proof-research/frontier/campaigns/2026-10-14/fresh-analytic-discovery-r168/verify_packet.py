#!/usr/bin/env python3
"""Read-only exact-packet check. Three detached SHA256 anchors are mandatory.
This verifies bytes and membership, not mathematical assertions.
"""
import argparse, hashlib, json, os
from pathlib import Path, PurePosixPath

EXCLUDED_FILES = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.sha256'}
EXCLUDED_DIR = 'private/seal-controls'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def selected_paths(root):
    paths = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        base = Path(directory)
        kept = []
        for name in dirs:
            p = base/name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                raise ValueError('symlink directory: '+rel)
            if rel != EXCLUDED_DIR:
                kept.append(name)
        dirs[:] = kept
        for name in files:
            p = base/name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                raise ValueError('symlink file: '+rel)
            if rel not in EXCLUDED_FILES:
                paths.add(rel)
    return paths

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root')
    ap.add_argument('--final',required=True)
    ap.add_argument('--manifest',required=True)
    ap.add_argument('--report',required=True)
    a=ap.parse_args()
    root=Path(a.root).resolve(strict=True)
    for name,anchor in [('FINAL.md',a.final),('MANIFEST.json',a.manifest),('REPORT.md',a.report)]:
        if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):
            raise ValueError('invalid explicit anchor for '+name)
        p=root/name
        if p.is_symlink() or digest(p.read_bytes())!=anchor:
            raise ValueError('detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    expected=set()
    for entry in m['files']:
        rel=entry['path'];pp=PurePosixPath(rel)
        if pp.is_absolute() or '..' in pp.parts or str(pp)!=rel or rel in expected:
            raise ValueError('unsafe/duplicate manifest path')
        if rel in EXCLUDED_FILES or rel==EXCLUDED_DIR or rel.startswith(EXCLUDED_DIR+'/'):
            raise ValueError('reserved path in packet')
        p=root/rel
        if p.is_symlink() or not p.is_file() or root not in p.resolve().parents:
            raise ValueError('invalid file: '+rel)
        data=p.read_bytes()
        if len(data)!=entry['bytes'] or digest(data)!=entry['sha256']:
            raise ValueError('payload mismatch: '+rel)
        expected.add(rel)
    if 'FINAL.md' not in expected:
        raise ValueError('FINAL missing from selected packet')
    actual=selected_paths(root)
    if actual!=expected:
        raise ValueError('packet membership mismatch; extra='+repr(sorted(actual-expected))+', missing='+repr(sorted(expected-actual)))
    print('Artifact bytes and exact membership verified:',len(expected),'files. No mathematical gate.')

if __name__=='__main__':
    main()
