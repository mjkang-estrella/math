#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Author: Myeongjin Kang; no affiliation.
"""Read-only integrity verifier. No mathematical or contribution truth check.

External --anchor is mandatory and checked before parsing any package JSON.
The seal binds manifest bytes; the manifest excludes itself and the seal.
Optional --original-author compares the independently anchored live original.
All context checks use internal snapshots; no live ledger dependency exists.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

sys.dont_write_bytecode = True
AUTHOR_ANCHOR = '056fc8c98bbdcd01a701ed94db722bcba07a9ea983e4c4459be34f875abfa657'
CANDIDATE = '2775917ef598b09507fbc217054e4ca8c65a8e377774bea3214929886ab7aab7'
SCOPE = '3348c130c424d6f753a39c6529cff81c0d923c3bb8d1eeb395327abb6734dc0f'
REVISION = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
HEX = re.compile(r'[0-9a-f]{64}')
PART = re.compile(r'[A-Za-z0-9._-]+')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    out = {}
    for key, value in items:
        require(key not in out, 'duplicate JSON key')
        out[key] = value
    return out


def parse(data):
    return json.loads(data, object_pairs_hook=pairs)


def safe(rel):
    require(isinstance(rel, str) and bool(rel), 'empty/non-string path')
    p = PurePosixPath(rel)
    require(not p.is_absolute() and p.as_posix() == rel, 'noncanonical path')
    require(all(x not in ('', '.', '..', '__pycache__') and PART.fullmatch(x)
                for x in rel.split('/')), 'unsafe path component')
    require(p.suffix not in ('.pyc', '.pyo'), 'bytecode forbidden')
    return rel


def read(root, rel):
    safe(rel)
    cur = root
    require(not cur.is_symlink() and cur.is_dir(), 'unsafe root')
    for component in rel.split('/')[:-1]:
        cur = cur / component
        mode = cur.lstat().st_mode
        require(stat.S_ISDIR(mode) and not stat.S_ISLNK(mode), 'unsafe parent')
    path = root / rel
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), 'nonregular file')
        return stream.read()


def inventory(root):
    require(not root.is_symlink() and root.is_dir(), 'unsafe tree root')
    files, dirs, inodes = set(), {'.'}, set()
    for directory, subdirs, names in os.walk(root, followlinks=False):
        for name in subdirs + names:
            path = Path(directory) / name
            rel = path.relative_to(root).as_posix()
            safe(rel)
            st = path.lstat()
            require(not stat.S_ISLNK(st.st_mode), 'symlink forbidden: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.add(rel)
            else:
                require(stat.S_ISREG(st.st_mode), 'special file forbidden')
                inode = (st.st_dev, st.st_ino)
                require(inode not in inodes, 'aliased file inode')
                inodes.add(inode)
                require(rel not in files, 'duplicate file member')
                files.add(rel)
    return files, dirs


def descriptor(root, row):
    require(set(row) == {'path', 'size', 'sha256'}, 'bad descriptor keys')
    rel = safe(row['path'])
    require(type(row['size']) is int and row['size'] >= 0, 'invalid size')
    require(isinstance(row['sha256'], str) and HEX.fullmatch(row['sha256']),
            'invalid SHA256')
    data = read(root, rel)
    require(len(data) == row['size'] and sha(data) == row['sha256'],
            'size/hash mismatch: ' + rel)
    return rel, data


def exact(root, expected):
    files, dirs = inventory(root)
    require(files == expected, 'file membership mismatch')
    expected_dirs = {str(q) for p in expected for q in PurePosixPath(p).parents}
    require(dirs == expected_dirs, 'directory membership mismatch')
    return len(files), len(dirs)


def author(root):
    raw = read(root, 'seal.json')
    require(sha(raw) == AUTHOR_ANCHOR, 'wrong author external anchor')
    seal = parse(raw)
    require(seal['revision'] == REVISION and seal['counted'] is False,
            'author revision/count metadata')
    require(seal['scope_sha256'] == SCOPE, 'author scope seal')
    expected = {'seal.json', 'seal.sha256'}
    require(read(root, 'seal.sha256') == (AUTHOR_ANCHOR + '  seal.json\n').encode(),
            'author detached digest bytes')
    manifests = []
    for key in ('inputs', 'outputs', 'receipt'):
        rel, data = descriptor(root, seal[key])
        require(rel not in expected, 'duplicate author descriptor')
        expected.add(rel)
        if key != 'receipt':
            manifests.append(data)
    for raw_manifest in manifests:
        m = parse(raw_manifest)
        require(m['format'] == 'sha256-size-v1', 'author manifest format')
        for row in m['files']:
            rel, _ = descriptor(root, row)
            require(rel not in expected, 'duplicate author member')
            expected.add(rel)
    counts = exact(root, expected)
    require(counts == (50, 12), 'author counts')
    require(sha(read(root, 'candidate.md')) == CANDIDATE, 'candidate identity')
    require(sha(read(root, 'original-scope.md')) == SCOPE, 'scope identity')
    return expected, counts


def run():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--original-author', type=Path)
    args = ap.parse_args()
    require(HEX.fullmatch(args.anchor) is not None, 'invalid external anchor')
    root = Path(__file__).absolute().parent
    # No JSON package parsing occurs before this required external check.
    seal_bytes = read(root, 'seal.json')
    require(sha(seal_bytes) == args.anchor, 'wrong review external anchor')
    seal = parse(seal_bytes)
    require(set(seal) == {'format', 'manifest'}, 'bad review seal keys')
    require(seal['format'] == 'nodal-power-four-review-r1-seal-v1', 'seal format')
    manifest_rel, manifest_bytes = descriptor(root, seal['manifest'])
    require(manifest_rel == 'manifest.json', 'manifest filename')
    manifest = parse(manifest_bytes)
    require(set(manifest) == {'format', 'files'}, 'manifest keys')
    require(manifest['format'] == 'sha256-size-v1', 'manifest format')
    expected = {'manifest.json', 'seal.json'}
    for row in manifest['files']:
        rel, _ = descriptor(root, row)
        require(rel not in expected, 'self-reference/duplicate member')
        expected.add(rel)
    package_counts = exact(root, expected)
    aroot = root / 'inputs/author'
    author_expected, author_counts = author(aroot)
    require(sha(read(root, 'original-scope.md')) == SCOPE, 'immutable scope copy')
    require(read(root, 'original-scope.md') == read(aroot, 'original-scope.md'),
            'scope copy mismatch')
    status = parse(read(root, 'status.json'))
    require(status['mathematics'] == 'PASS_FULL_T4' and
            status['contribution'] == 'TECHNICAL' and
            status['author_proof'] == 'NEEDS_REVISION' and
            status['reviewer_repairs_required'] is True and
            status['counted'] is False and status['campaign_count'] == '4/10',
            'verdict/count metadata')
    require(status['scope_sha256'] == SCOPE and status['candidate_sha256'] == CANDIDATE,
            'status immutable identities')
    tree = parse(read(root, 'inputs/context/preprints-tree.json'))
    require(tree['truncated'] is False and len(tree['tree']) == 13223,
            'complete catalogue contract')
    all_paths = [e['path'] for e in tree['tree']]
    require(len(set(all_paths)) == len(all_paths), 'duplicate catalogue path')
    index = {e['path']: e for e in tree['tree'] if e['type'] == 'blob'}
    upstream = parse(read(root, 'inputs/context/upstream.json'))
    require(upstream['commit'] == REVISION, 'upstream revision')
    identities = parse(read(aroot, 'git-identities.json'))
    require(identities['revision'] == REVISION and len(identities['files']) == 31,
            'pinned identity contract')
    locals_seen, upstream_seen = set(), set()
    for entry in identities['files']:
        local = safe(entry['local'])
        remote = safe(entry['upstream_path'])
        require(local not in locals_seen and remote not in upstream_seen,
                'duplicate source identity')
        locals_seen.add(local)
        upstream_seen.add(remote)
        data = read(aroot, local)
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        target = index[remote]
        require(blob == entry['git_blob_sha1'] == target['sha'] and
                len(data) == entry['size'] == target['size'] and
                sha(data) == entry['sha256'], 'pinned Git blob mismatch')
    require(locals_seen == {p for p in author_expected if p.startswith('inputs/pinned/')},
            'pinned membership mismatch')
    if args.original_author is not None:
        live = args.original_author.absolute()
        live_expected, live_counts = author(live)
        require(live_expected == author_expected and live_counts == author_counts,
                'original author membership mismatch')
        for rel in author_expected:
            require(read(live, rel) == read(aroot, rel), 'original author changed: ' + rel)
    print(json.dumps({'result': 'PASS_INTEGRITY_ONLY',
                      'review_files': package_counts[0],
                      'review_directories_including_root': package_counts[1],
                      'author_files': author_counts[0],
                      'author_directories_including_root': author_counts[1],
                      'pinned_blobs': len(locals_seen), 'catalogue_entries': len(tree['tree']),
                      'external_anchor_required_and_checked_first': True,
                      'original_author_compared': args.original_author is not None,
                      'live_context_dependencies': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        run()
    except Exception as exc:
        print('FAIL_INTEGRITY: ' + str(exc), file=sys.stderr)
        sys.exit(1)
