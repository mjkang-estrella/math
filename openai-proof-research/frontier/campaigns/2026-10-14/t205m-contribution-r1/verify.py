#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Identity-only verification of the T205M contribution review packet.

Requires the externally reported SHA-256 of manifest.json. Checks exact
membership of this directory, then re-hashes the anchored author files
(read-only) and the privately retrieved primary PDFs. No mathematical or
contribution verdict is recomputed.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import stat

AUTHOR_ANCHORS = {
    'manifest.json': '29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9',
    'verify.py': '5b27e887a79adc22c0c00fc1fa730eabd6fac0a249aec9df24083691f0e8bf1f',
    'candidate205m.md': '17b2b35c42ef10fd0600e0a7b4b5897f0b80cd57cfb1e12587b722294a3e20c5',
    'scope205m.md': '3eb9d790999b419a4083ead2a3ed0979217a36a12bdd78ceabe7fa6d3afb64f6',
    'source-and-credit.md': 'fe5d374d77c5140afda55bb5bfe7aba2393cbed0b8da3ef2fd80c613b1da5e2c',
    'kostka-low-capacity-proof.md': 'd8e029e92d03e946687c4601b6e92afdc6cad8607c2bf564b95af0a2a6ed6ea8',
    'provenance/parent-high-capacity.md': 'fc155c9ac03d70b8a68f501541daf0fb5c02bf9caf6734f61757065a6e796430',
    'finite-proof-certificate.json': '5ffb18808a16add627497b29c82ee389187ad8f4d6df0f6fa52cc6ab49d99263',
}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def inventory(base):
    files, dirs = set(), set()
    for root, dirnames, filenames in os.walk(base):
        for name in dirnames + filenames:
            path = Path(root) / name
            rel = path.relative_to(base).as_posix()
            info = os.lstat(path)
            require(not stat.S_ISLNK(info.st_mode), f'symlink: {rel}')
            if stat.S_ISDIR(info.st_mode):
                dirs.add(rel)
            else:
                require(stat.S_ISREG(info.st_mode), f'nonregular entry: {rel}')
                require(info.st_nlink == 1, f'hardlink: {rel}')
                files.add(rel)
    return files, dirs


def membership(expected, actual, what):
    require(expected == actual, f'{what} inventory mismatch: '
            f'missing={sorted(expected - actual)}, extra={sorted(actual - expected)}')


def verify_own(base, anchor):
    require(os.path.realpath(base) == str(base), 'non-canonical or symlinked ancestor path')
    raw = (base / 'manifest.json').read_bytes()
    require(digest(raw) == anchor, 'external manifest anchor mismatch')
    manifest = json.loads(raw)
    expected = {}
    for row in manifest['files']:
        name = row['path']
        path = PurePosixPath(name)
        require(name == path.as_posix() and not path.is_absolute() and '..' not in path.parts,
                'noncanonical manifest path')
        require(name not in expected and name != 'manifest.json', 'duplicate or reserved path')
        require(path.name != 'manifest.json', 'nested manifest')
        expected[name] = row
    files, dirs = inventory(base)
    files.discard('manifest.json')
    require(not any(PurePosixPath(f).name == 'manifest.json' for f in files), 'nested manifest')
    membership(set(expected), files, 'file')
    membership(set(manifest['directories']), dirs, 'directory')
    for name, row in expected.items():
        data = (base / name).read_bytes()
        require(len(data) == row['bytes'] and digest(data) == row['sha256'], f'bytes: {name}')
    return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--anchor', required=True, help='external SHA-256 of manifest.json')
    parser.add_argument('--author-root', help='author packet (default: sibling directory)')
    args = parser.parse_args()
    base = Path(os.path.abspath(__file__)).parent
    own = verify_own(base, args.anchor)
    author = Path(args.author_root) if args.author_root else \
        base.parent / 'fresh-arithmetic-discovery-r38'
    for name, sha in AUTHOR_ANCHORS.items():
        require(digest((author / name).read_bytes()) == sha, f'author anchor mismatch: {name}')
    binding = json.loads((base / 'input-binding.json').read_text())
    require(binding['author_anchors'] == AUTHOR_ANCHORS, 'binding/anchor disagreement')
    require(binding['source_pin'] == PIN, 'pin mismatch')
    rows = json.loads((base / 'primary-retrieval.json').read_text())
    for row in rows:
        data = (base / row['file']).read_bytes()
        require(len(data) == row['bytes'] and digest(data) == row['sha256'], f'primary: {row["file"]}')
        require(digest((base / row['text_file']).read_bytes()) == row['text_sha256'],
                f'primary text: {row["text_file"]}')
    print(json.dumps({'result': 'IDENTITY_ONLY_PASS', 'verdict_recorded': own['verdict'],
                      'review_payloads': len(own['files']), 'directories': len(own['directories']),
                      'author_anchors_checked': len(AUTHOR_ANCHORS), 'primary_pdfs': len(rows),
                      'writes': 0, 'count_changed': False}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit('REJECT: ' + str(exc))
