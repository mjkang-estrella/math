#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""External-anchor/exact-membership verification; no mathematical verdict check."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json

AUTHOR_ANCHOR = '581d8051354ede8bed18853f82c8a87726df5223a7d912b7aa00054d87658481'
SCOPE_ANCHOR = '8f3721124a0e1d78e567221d97f188e0416587bd6b40aeb7615f4346df7e6de3'
PROOF_ANCHOR = '35085a430f183cd16a4ee6dcd8eca293739a633e0df2da2c094f4dfbaaef7667'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def membership(expected, actual, what):
    require(expected == actual, f'{what} membership mismatch: '
            f'missing={sorted(expected-actual)}, extra={sorted(actual-expected)}')


def verify_packet(base, anchor):
    raw = (base / 'manifest.json').read_bytes()
    require(digest(raw) == anchor, f'{base.name}: external manifest anchor mismatch')
    manifest = json.loads(raw)
    expected = {}
    for row in manifest['files']:
        name = row['path']
        path = PurePosixPath(name)
        require(name == path.as_posix() and not path.is_absolute() and '..' not in path.parts,
                'noncanonical manifest path')
        require(name not in expected and name != 'manifest.json', 'duplicate/reserved path')
        expected[name] = row
    actual, dirs = set(), set()
    for path in base.rglob('*'):
        require(not path.is_symlink(), 'symlink')
        rel = path.relative_to(base).as_posix()
        if path.is_dir():
            dirs.add(rel)
        else:
            require(path.is_file(), 'special file')
            if rel != 'manifest.json':
                actual.add(rel)
    membership(set(expected), actual, 'file')
    membership(set(manifest['directories']), dirs, 'directory')
    for name, row in expected.items():
        raw = (base / name).read_bytes()
        require(len(raw) == row['bytes'] and digest(raw) == row['sha256'], f'bytes: {name}')
    # Non-mutating checks of both exact-membership rejection branches.
    for simulated in (actual | {'__unexpected__'}, actual - {next(iter(actual))}):
        try:
            membership(set(expected), simulated, 'selfcheck')
        except ValueError:
            pass
        else:
            raise ValueError('membership rejection selfcheck failed')
    return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    own = verify_packet(base, args.anchor)
    author = base / 'private/author'
    frozen = verify_packet(author, AUTHOR_ANCHOR)
    require(digest((author/'scope.json').read_bytes()) == SCOPE_ANCHOR, 'scope anchor mismatch')
    require(digest((author/'rank-isolation.md').read_bytes()) == PROOF_ANCHOR, 'proof anchor mismatch')
    sources = json.loads((author/'source-receipt.json').read_text())
    tree = json.loads((base/'private/source-tree-extract.json').read_text())
    require(sources['pin'] == tree['pin'] == PIN, 'pin mismatch')
    blobs = {row['path']: row['sha'] for row in tree['entries']}
    membership(set(blobs), {row['path'] for row in sources['sources']}, 'source-tree')
    for row in sources['sources']:
        raw = (author/row['local']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob == row['git_blob'] == blobs[row['path']], 'Git blob mismatch')
        require(digest(raw) == row['sha256'], 'source SHA256 mismatch')
    primary = json.loads((author/'private/primary-receipt.json').read_text())
    retrieved = {row['url']: row for row in json.loads((base/'independent-primary-retrieval.json').read_text())}
    for row in primary:
        raw = (author/'private'/row['file']).read_bytes()
        require(len(raw) == row['bytes'] and digest(raw) == row['sha256'], 'primary PDF bytes')
        require(retrieved[row['url']]['matches_author'] is True and
                retrieved[row['url']]['sha256'] == row['sha256'], 'fresh retrieval mismatch')
    print(json.dumps({'result':'IDENTITY_ONLY','review_payloads':len(own['files']),
                      'author_payloads':len(frozen['files']),'pinned_blobs':len(blobs),
                      'primary_PDFs':len(primary),'scope_anchor':SCOPE_ANCHOR,
                      'proof_anchor':PROOF_ANCHOR,'external_contexts_bound':False,
                      'missing_extra_selfchecks':'passed','writes':0,'count_changed':False}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as exc:
        raise SystemExit('REJECT: '+str(exc))
