#!/usr/bin/env python3
"""Read-only integrity verifier. Requires three detached SHA256 anchors.
Run with python -B. This is not a proof, rights, novelty or acceptance review.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_HASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def ordinary(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'nonordinary file: ' + str(path))
    return s

def read(path):
    ordinary(path)
    return path.read_bytes()

def safe(base, relative):
    p = PurePosixPath(relative)
    require(bool(relative) and not p.is_absolute() and all(x not in ('', '.', '..') for x in relative.split('/')), 'unsafe relative path')
    require('\\' not in relative, 'backslash in path')
    return base.joinpath(*p.parts)

def inventory(base):
    files, dirs = {}, {}
    require(not base.is_symlink() and base.is_dir(), 'bad packet root')
    for here, children, names in os.walk(base, followlinks=False):
        for name in children:
            p = Path(here) / name
            s = p.lstat()
            require(stat.S_ISDIR(s.st_mode) and not p.is_symlink(), 'nonordinary directory: ' + str(p))
            dirs[p.relative_to(base).as_posix()] = stat.S_IMODE(s.st_mode)
        for name in names:
            p = Path(here) / name
            s = ordinary(p)
            b = p.read_bytes()
            files[p.relative_to(base).as_posix()] = {'sha256': digest(b), 'size': len(b), 'mode': stat.S_IMODE(s.st_mode)}
    return files, dirs

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    for key in ('final', 'manifest', 'report'):
        parser.add_argument('--' + key + '-sha256', required=True)
    parser.add_argument('--original-project', type=Path)
    args = parser.parse_args()
    root = args.root
    require(root.is_dir() and not root.is_symlink(), 'bad outer root')
    packet = root / 'packet'
    blobs = {}
    for key, p in [('final', packet/'FINAL.json'), ('manifest', packet/'MANIFEST.json'), ('report', root/'REPORT.md')]:
        expected = getattr(args, key + '_sha256')
        require(len(expected) == 64 and all(c in '0123456789abcdef' for c in expected), 'invalid detached anchor')
        blobs[key] = read(p)
        require(digest(blobs[key]) == expected, key + ' detached-anchor mismatch')
    final, manifest = json.loads(blobs['final']), json.loads(blobs['manifest'])
    require(final['manifest_sha256'] == args.manifest_sha256, 'FINAL manifest mismatch')
    require(final['outside_report_sha256'] == args.report_sha256, 'FINAL report mismatch')
    require(final['status'] == 'PREFREEZE' and final['nominee'] is None and final['frozen_candidate'] is None, 'wrong outcome metadata')
    require(final['pinned_commit'] == PIN, 'wrong pin metadata')
    files, dirs = inventory(packet)
    expected = manifest['payloads']
    require(set(files) == set(expected) | {'FINAL.json', 'MANIFEST.json'}, 'exact file inventory mismatch')
    require(dirs == manifest['directories'], 'exact directory inventory/mode mismatch')
    for name, record in expected.items():
        safe(packet, name)
        require(files[name] == record, 'payload mismatch: ' + name)
    for name in ('FINAL.json', 'MANIFEST.json'):
        require(files[name]['mode'] == manifest['seal_mode'], 'seal file mode mismatch')
    require(stat.S_IMODE(ordinary(root/'REPORT.md').st_mode) == manifest['report_mode'], 'report mode mismatch')
    require(len(expected) == final['payload_count'] and len(dirs) == final['directory_count'], 'count metadata mismatch')
    context = packet/'private/context'
    tree_bytes = read(context/'sources/preprints-tree.json')
    require(digest(tree_bytes) == TREE_HASH, 'complete tree hash mismatch')
    tree = json.loads(tree_bytes)
    require(tree.get('truncated') is False and len(tree['tree']) == 13223, 'incomplete preprint tree')
    entries = {x['path']: x for x in tree['tree']}
    receipts = json.loads(read(packet/'private/sources/acquisition.json'))
    require(len({x['path'] for x in receipts}) == len(receipts), 'duplicate source receipts')
    for x in receipts:
        b = read(safe(packet/'private/sources', x['path']))
        g = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        t = entries[x['path']]
        require(t['type'] == 'blob' and len(b) == t['size'] == x['size'], 'pinned size mismatch')
        require(g == t['sha'] == x['git_blob'] and digest(b) == x['sha256'], 'pinned blob/hash mismatch')
        require(x['url'] == 'https://raw.githubusercontent.com/openai/math/' + PIN + '/' + x['path'], 'nonpinned source URL')
    primary = json.loads(read(packet/'private/primary/acquisition.json'))
    count = 0
    for x in primary:
        if 'error' in x:
            continue
        b = read(packet/'private/primary'/(x['version']+'.pdf'))
        require(len(b) == x['bytes'] and digest(b) == x['sha256'], 'primary receipt mismatch')
        require(x['url'] == 'https://arxiv.org/pdf/' + x['version'], 'primary URL/version mismatch')
        count += 1
    stable, observed = 0, []
    for folder in ('context', 'history'):
        base = packet/'private'/folder
        for x in json.loads(read(base/'bindings.json')):
            b = read(safe(base, x['path']))
            require(len(b) == x['size'] and digest(b) == x['sha256'], 'copied input binding mismatch')
            if args.original_project:
                original = safe(args.original_project, x['path'])
                require(not original.is_symlink(), 'symlink original')
                b2 = original.read_bytes()
                same = len(b2) == x['size'] and digest(b2) == x['sha256']
                if x['kind'] == 'stable_input':
                    require(same, 'current stable original changed: ' + x['path'])
                    stable += 1
                else:
                    observed.append({'path': x['path'], 'currently_matches_observation': same})
    print(json.dumps({'artifact_integrity': 'PASS', 'mathematical_review': 'NOT_PERFORMED', 'payloads': len(expected), 'directories': len(dirs), 'pinned_blobs': len(receipts), 'primary_pdfs': count, 'stable_originals_compared': stable, 'mutable_observations': observed}, indent=2))

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'artifact_integrity': 'FAIL', 'reason': str(error)}))
        sys.exit(1)
