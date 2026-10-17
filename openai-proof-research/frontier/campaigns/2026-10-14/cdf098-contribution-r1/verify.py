#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only identity verification. No mathematical certification."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path, PurePosixPath

AUTHOR = 'f417cfd409e18a34c97f488fb10ebfa25f1b09b5fc4ff323c53c71cf71262c85'
SCOPE = 'bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5'
PROOF = '24c5d7055f19b48bac26451a87896845756865eeeba5d0502e1f7982ccb6f39a'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--anchor', required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'manifest.json').read_bytes()
    need(sha(raw) == args.anchor, 'external review anchor mismatch')
    manifest = json.loads(raw)
    names = set()
    for row in manifest['files']:
        name = row['path']
        p = PurePosixPath(name)
        need(not p.is_absolute() and '..' not in p.parts and p.as_posix() == name,
             'unsafe path')
        need(name not in names and name != 'manifest.json', 'duplicate/root manifest')
        names.add(name)
        data = (root / name).read_bytes()
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'payload ' + name)
    files, dirs = set(), set()
    for p in root.rglob('*'):
        need(not p.is_symlink(), 'symlink')
        name = p.relative_to(root).as_posix()
        if p.is_dir():
            dirs.add(name)
        else:
            need(p.is_file(), 'special file')
            files.add(name)
    need(files == names | {'manifest.json'}, 'exact file membership')
    need(dirs == set(manifest['directories']), 'exact directory membership')
    author = root / 'private/author'
    need(sha((author / 'manifest.json').read_bytes()) == AUTHOR, 'author anchor')
    need(sha((author / 'original-scope.md').read_bytes()) == SCOPE, 'scope anchor')
    need(sha((author / 'candidate.md').read_bytes()) == PROOF, 'proof anchor')
    result = subprocess.run([sys.executable, str(author / 'verify.py'), '--anchor', AUTHOR],
                            check=True, capture_output=True, text=True)
    author_result = json.loads(result.stdout)
    primary = json.loads((root / 'private/new-primary-receipt.json').read_text())
    for row in primary:
        data = (root / 'private' / (row['name'] + '.pdf')).read_bytes()
        need(data.startswith(b'%PDF') and len(data) == row['bytes'] and
             sha(data) == row['sha256'], 'new primary PDF')
    print(json.dumps(dict(result='INTEGRITY_ONLY', review_payloads=len(names),
                          author_payloads=author_result['payloads'],
                          pinned_text_blobs=author_result['pinned_text_blobs'],
                          primary_pdfs=author_result['primary_PDFs'] + len(primary),
                          mathematical_certification=False, count_changed=False)))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError, subprocess.CalledProcessError) as exc:
        raise SystemExit('REJECT: ' + str(exc))
