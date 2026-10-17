#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only external-anchor verification; does not certify mathematics.
Path/JSON safeguards follow the inspected CM275 author verifier, with original
review-specific identity checks. No author mathematical code is executed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

def check(value, message):
    if not value:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def unique(pairs):
    result = {}
    for key, value in pairs:
        check(key not in result, 'duplicate JSON key')
        result[key] = value
    return result

def read_json(raw):
    return json.loads(raw, object_pairs_hook=unique)

def path_name(name):
    check(isinstance(name, str) and name and '\\' not in name, 'bad path')
    p = PurePosixPath(name)
    check(not p.is_absolute() and p.as_posix() == name, 'noncanonical path')
    check(all(x not in ('.', '..', '__pycache__') for x in p.parts), 'unsafe path')
    check(not name.endswith(('.pyc', '.pyo')), 'bytecode forbidden')
    return name

def inventory(root, manifest):
    expected = {}
    for rec in manifest['files']:
        name = path_name(rec['path'])
        check(name not in expected and name != 'output-manifest.json', 'duplicate/self file')
        expected[name] = rec
    expected_dirs = [path_name(x) for x in manifest['directories']]
    check(len(expected_dirs) == len(set(expected_dirs)), 'duplicate directory')
    files, dirs = set(), set()
    for folder, subdirs, names in os.walk(root, followlinks=False):
        for name in subdirs + names:
            p = Path(folder) / name
            rel = path_name(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            check(not stat.S_ISLNK(mode), 'symlink')
            if stat.S_ISDIR(mode):
                dirs.add(rel)
            else:
                check(stat.S_ISREG(mode), 'nonregular file')
                files.add(rel)
    check(files == set(expected) | {'output-manifest.json'}, 'file membership')
    check(dirs == set(expected_dirs), 'directory membership')
    for name, rec in expected.items():
        data = (root / name).read_bytes()
        check(len(data) == rec['bytes'] and sha(data) == rec['sha256'], 'payload: ' + name)
    return len(expected), len(dirs)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--anchor', required=True)
    parser.add_argument('--author-root', type=Path)
    args = parser.parse_args()
    check(re.fullmatch('[0-9a-f]{64}', args.anchor) is not None, 'bad anchor')
    root = Path(__file__).absolute().parent
    check(not root.is_symlink(), 'root symlink')
    seal = root / 'output-manifest.json'
    check(not seal.is_symlink(), 'manifest symlink')
    raw = seal.read_bytes()
    check(sha(raw) == args.anchor, 'external anchor mismatch')
    manifest = read_json(raw)
    check(manifest['schema'] == 'CM275-independent-contribution-v1', 'schema')
    count, directories = inventory(root, manifest)
    decision = read_json((root / 'decision.json').read_bytes())
    for name, key in [('output-manifest.json', 'author_manifest_sha256'),
                      ('candidate.md', 'candidate_sha256'),
                      ('original-scope.md', 'scope_sha256')]:
        check(sha((root / 'inputs' / name).read_bytes()) == decision[key], 'reviewed identity')
    check(decision['verdict'] == 'SUBSTANTIAL' and decision['proof_verdict'] is None,
          'role/verdict mismatch')
    author_checked = False
    if args.author_root is not None:
        author = args.author_root.absolute()
        check(not author.is_symlink(), 'author root symlink')
        source_manifest = author / 'output-manifest.json'
        check(not source_manifest.is_symlink(), 'author manifest symlink')
        author_raw = source_manifest.read_bytes()
        check(sha(author_raw) == decision['author_manifest_sha256'], 'author anchor mismatch')
        inventory(author, read_json(author_raw))
        receipts = read_json((author / 'input-manifest.json').read_bytes())
        for rec in receipts['pinned_blobs']:
            data = (author / path_name(rec['local'])).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            check(blob == rec['git_blob'], 'source Git identity')
        author_checked = True
    print(json.dumps({'integrity': 'PASS', 'payload_files': count,
                      'directories': directories, 'reviewed_author_checked': author_checked,
                      'recorded_contribution_verdict': decision['verdict'],
                      'integrity_is_mathematical_verification': False}))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print('REJECT: ' + str(exc), file=sys.stderr)
        sys.exit(1)
