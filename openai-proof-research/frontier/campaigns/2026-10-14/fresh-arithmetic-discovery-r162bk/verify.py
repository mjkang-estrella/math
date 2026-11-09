#!/usr/bin/env python3
"""Read-only r162bk packet verifier; explicit detached anchors required."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT = PROJECT / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bk'
RESERVED = {'MANIFEST.json', 'REPORT.md'}
ORIGINALS = (
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bj-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bj/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bj/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bj/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bj/FINAL.md',
)
PREFIXES = (
 'preprints/uniform-bounds-for-planar-polynomial-limit-cycles-September-24-2026/',
 'preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/',
)

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def anchor(data, expected, label):
    require(len(expected) == 64 and all(c in '0123456789abcdef' for c in expected), label + ': malformed anchor')
    require(sha(data) == expected, label + ': anchor mismatch')

def safe(name, directory=False):
    require(isinstance(name, str), 'nonstring path')
    if directory and name == '.':
        return
    p = PurePosixPath(name)
    require(not p.is_absolute() and '\\' not in name and str(p) == name and all(x not in ('', '.', '..') for x in p.parts), 'unsafe path: ' + name)

def inventory(root):
    require(root.is_dir() and not root.is_symlink(), 'invalid root')
    files, dirs = [], []
    for base, subdirs, names in os.walk(root, followlinks=False):
        bp = Path(base)
        rel = bp.relative_to(root).as_posix()
        require(not bp.is_symlink(), 'directory symlink')
        dirs.append({'path': rel, 'mode': bp.lstat().st_mode})
        for name in subdirs:
            require(not (bp / name).is_symlink(), 'symlink directory: ' + name)
        for name in names:
            p = bp / name
            require(stat.S_ISREG(p.lstat().st_mode), 'nonregular member: ' + str(p))
            rel = p.relative_to(root).as_posix()
            if rel in RESERVED:
                continue
            b = p.read_bytes()
            files.append({'path': rel, 'mode': p.lstat().st_mode, 'bytes': len(b), 'sha256': sha(b)})
    return sorted(files, key=lambda x:x['path']), sorted(dirs, key=lambda x:x['path'])

def check_payload(root, doc):
    require(doc['format'] == 'r162bk-1', 'format')
    for key in ('files', 'directories'):
        paths = [x['path'] for x in doc[key]]
        require(paths == sorted(paths) and len(paths) == len(set(paths)), key + ': unsorted or duplicate')
        for p in paths:
            safe(p, key == 'directories')
    require(not (set(x['path'] for x in doc['files']) & RESERVED), 'reserved payload')
    files, dirs = inventory(root)
    require(files == doc['files'], 'payload membership/hash/length/mode mismatch')
    require(dirs == doc['directories'], 'directory membership/mode mismatch')

def check_bindings(root):
    source = json.loads((root / 'private/source-authentication.json').read_bytes())
    seen = set()
    for row in source:
        name = row['path']; safe(name)
        require(any(name.startswith(p) for p in PREFIXES), 'source prefix')
        require(name not in seen, 'duplicate source'); seen.add(name)
        b = (root / 'private/canonical' / name).read_bytes()
        require(len(b) == row['bytes'] and sha(b) == row['sha256'], 'source binding')
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        require(blob == row['git_blob'], 'source Git blob')
    require(len(source) == 33, 'source count')
    initial = json.loads((root / 'private/completed.json').read_bytes())
    late = json.loads((root / 'private/completed-late-modes.json').read_bytes())
    require(tuple(x['original'] for x in initial) == ORIGINALS, 'completed originals')
    require(tuple(x['original'] for x in late) == ORIGINALS, 'late originals')
    for i,(row,last) in enumerate(zip(initial,late)):
        require(row['copy'] == 'private/completed/' + str(i), 'completed copy path')
        p = PROJECT / ORIGINALS[i]
        require(not p.is_symlink() and stat.S_ISREG(p.lstat().st_mode), 'original file kind')
        b = p.read_bytes()
        require(len(b) == row['bytes'] == last['bytes'], 'original length')
        require(sha(b) == row['sha256'] == last['sha256'], 'original hash')
        require(stat.S_IMODE(p.lstat().st_mode) == int(row['mode'],8), 'initial permissions')
        require(p.lstat().st_mode == last['full_mode'], 'later full mode')
        require((root / row['copy']).read_bytes() == b, 'copy equality')

def verify(root, final_sha, manifest_sha, report_sha):
    require(root.resolve() == ROOT.resolve(), 'wrong packet root')
    for name, expected in [('FINAL.md', final_sha), ('MANIFEST.json', manifest_sha), ('REPORT.md', report_sha)]:
        anchor((root/name).read_bytes(), expected, name)
    doc = json.loads((root/'MANIFEST.json').read_bytes())
    check_payload(root,doc)
    check_bindings(root)
    require(doc['final_sha256'] == final_sha, 'manifest FINAL binding')
    for name in RESERVED:
        require((root/name).lstat().st_mode == doc['reserved_modes'][name], 'reserved mode')
    return len(doc['files']), sum(x['bytes'] for x in doc['files']), len(doc['directories'])

if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--final',required=True)
    ap.add_argument('--manifest',required=True)
    ap.add_argument('--report',required=True)
    args=ap.parse_args()
    n,b,d=verify(args.root,args.final,args.manifest,args.report)
    print(f'MATCH {n} payload files / {b} bytes / {d} directories including root; originals and copies unchanged')
