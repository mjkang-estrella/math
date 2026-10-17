#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only detached-manifest identity checks, not a mathematical proof checker."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

AUTHOR_ANCHOR = '2fabba39b9b907f675c01162eae65b970236923ed5b14b611017a515f7eef267'
CANDIDATE = 'e1e93a97ddae2d47d32feb0fa464da93c32d4de661c93b63ac0e7ff785de310a'
SCOPE = '4f4f5103561d77dd475a5b8f50bbcd0d8989e102c18392ace80cb0b52a735984'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root, anchor):
    require(not root.is_symlink(), 'symlink root')
    data = (root / 'manifest.json').read_bytes()
    require(sha(data) == anchor, 'external manifest anchor mismatch')
    manifest = json.loads(data)
    rows = manifest['files']
    names = [row['path'] for row in rows]
    require(len(names) == len(set(names)), 'duplicate inventory names')
    expected = set(names) | {'manifest.json'}
    files, dirs = set(), set()
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'symlink entry')
        name = p.relative_to(root).as_posix()
        if p.is_dir():
            dirs.add(name)
        elif p.is_file():
            files.add(name)
        else:
            raise ValueError('nonregular entry')
    require(files == expected, 'file membership mismatch')
    require(dirs == set(manifest['directories']), 'directory membership mismatch')
    for row in rows:
        path = Path(row['path'])
        require(not path.is_absolute() and '..' not in path.parts, 'unsafe path')
        blob = (root / path).read_bytes()
        require(len(blob) == row['bytes'] and sha(blob) == row['sha256'], 'payload mismatch: ' + str(path))
    return manifest

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    root = Path(__file__).absolute().parent
    own = inventory(root, args.anchor)
    author = root.parent / 'fresh-structural-discovery-r27'
    source = inventory(author, AUTHOR_ANCHOR)
    require(sha((author / 'candidate.md').read_bytes()) == CANDIDATE, 'candidate drift')
    require(sha((author / 'original-scope.md').read_bytes()) == SCOPE, 'scope drift')
    status = json.loads((root / 'status.json').read_text())
    require(status['verdict'] == 'PASS_FULL_TS132' and status['count_change'] == 0, 'verdict mismatch')
    require(status['full_scope_preserved'] and not status['formalized'], 'review scope mismatch')
    auth = json.loads((root / 'authentication.json').read_text())
    require(auth['final_author_manifest_sha256'] == AUTHOR_ANCHOR, 'author receipt mismatch')
    repo = root.parents[3]
    tree_raw = (repo / 'sources/preprints-tree.json').read_bytes()
    require(sha(tree_raw) == auth['tree_sha256'], 'complete tree drift')
    tree = json.loads(tree_raw)
    require(tree['truncated'] is False, 'truncated tree')
    entries = {item['path']: item for item in tree['tree']}
    upstream = json.loads((repo / 'sources/upstream.json').read_text())
    require(upstream['commit'] == PIN, 'source pin drift')
    receipt = json.loads((author / 'source-receipt.json').read_text())
    require(receipt['pin'] == PIN and len(receipt['files']) == 7, 'source receipt scope')
    for item in receipt['files']:
        blob = (author / item['local']).read_bytes()
        git = hashlib.sha1(b'blob ' + str(len(blob)).encode() + b'\0' + blob).hexdigest()
        key = item['path']
        if key not in entries:
            key = key.removeprefix('preprints/')
        require(git == item['git_blob'] == entries[key]['sha'], 'source Git blob mismatch')
        require(sha(blob) == item['sha256'], 'source SHA mismatch')
    family = 'A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/'
    family_paths = {item['path'].removeprefix('preprints/') for item in tree['tree']
                    if family in item['path'] and item['type'] == 'blob' and not item['path'].endswith('.pdf')}
    require(family_paths == {item['path'].removeprefix('preprints/') for item in receipt['files']}, 'source family completeness')
    print(json.dumps({'status': 'IDENTITY_ONLY', 'review_payloads': len(own['files']),
                      'author_payloads': len(source['files']), 'pinned_blobs': 7,
                      'recorded_verdict': status['verdict'], 'count_change': 0,
                      'mathematics_executed': False, 'writes': 0}, sort_keys=True))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print('REJECT: ' + str(error), file=sys.stderr)
        sys.exit(1)
