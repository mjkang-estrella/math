#!/usr/bin/env python3
"""Read-only integrity replay; original code MIT, Myeongjin Kang, no affiliation."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def unique(pairs):
    result = {}
    for k, v in pairs:
        need(k not in result, 'duplicate JSON key')
        result[k] = v
    return result


def parse(b):
    return json.loads(b, object_pairs_hook=unique)


def name(s):
    need(isinstance(s, str) and s and '\\' not in s, 'bad path')
    p = PurePosixPath(s)
    need(not p.is_absolute() and p.as_posix() == s, 'noncanonical path')
    need(all(t not in ('', '.', '..') for t in p.parts), 'unsafe path')
    return s


def inventory(root):
    need(root.is_dir() and not root.is_symlink(), 'bad root')
    files, directories = set(), set()
    for folder, dirs, fs in os.walk(root, followlinks=False):
        for n in dirs + fs:
            p = Path(folder) / n
            r = name(p.relative_to(root).as_posix())
            mode = p.lstat().st_mode
            need(not stat.S_ISLNK(mode), 'symlink: ' + r)
            if stat.S_ISDIR(mode):
                directories.add(r)
            else:
                need(stat.S_ISREG(mode), 'nonregular file')
                files.add(r)
    return files, directories


def authenticated_manifest(root, anchor, author=False):
    need(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'bad anchor')
    path = root / 'output-manifest.json'
    need(not path.is_symlink(), 'manifest symlink')
    data = path.read_bytes()
    need(sha(data) == anchor, 'external anchor mismatch')
    m = parse(data)
    if author:
        need(m['schema'] == 'CM275-exact-membership-v1', 'author schema')
        rows = m['files']
        expected = {}
        for row in rows:
            r = name(row['path'])
            need(r not in expected, 'duplicate payload')
            expected[r] = row['sha256']
    else:
        need(m['schema'] == 'CM275-proof-review-r1-v1', 'review schema')
        expected = {name(k): v for k, v in m['files'].items()}
    need('output-manifest.json' not in expected, 'self-listed manifest')
    directories = [name(d) for d in m['directories']]
    need(len(set(directories)) == len(directories), 'duplicate directory')
    fs, ds = inventory(root)
    need(fs == set(expected) | {'output-manifest.json'}, 'file membership')
    need(ds == set(directories), 'directory membership')
    for r, digest in expected.items():
        need(sha((root / r).read_bytes()) == digest, 'payload hash: ' + r)
    if author:
        for row in rows:
            need((root / row['path']).stat().st_size == row['bytes'], 'author size')
    return m, len(expected)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--author-root', type=Path)
    a = ap.parse_args()
    root = a.root.absolute()
    author = (a.author_root or root.parent / 'fresh-analytic-discovery-r26').absolute()
    m, n = authenticated_manifest(root, a.anchor)
    receipt = parse((root / 'input-receipt.json').read_bytes())
    am, an = authenticated_manifest(author, receipt['external_manifest_anchor'], author=True)
    for r, digest in receipt['author_inputs'].items():
        need(sha((author / name(r)).read_bytes()) == digest, 'reviewed input: ' + r)
    need(am['candidate_sha256'] == m['candidate_sha256'], 'candidate identity')
    need(am['scope_sha256'] == m['scope_sha256'], 'scope identity')
    for fn in ['candidate.md', 'original-scope.md', 'freeze-receipt.json', 'output-manifest.json']:
        need((root / 'inputs' / ('author-' + fn)).read_bytes() == (author / fn).read_bytes(), 'snapshot drift')
    im = parse((author / 'input-manifest.json').read_bytes())
    need(im['pin'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb', 'source pin')
    for rec in im['pinned_blobs']:
        data = (author / name(rec['local'])).read_bytes()
        need(sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'source hash')
        need(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == rec['git_blob'], 'source Git blob')
    for rec in im['primary_pdfs']:
        data = (author / name(rec['local'])).read_bytes()
        need(data.startswith(b'%PDF-') and sha(data) == rec['sha256'] and len(data) == rec['bytes'], 'primary PDF')
    print(json.dumps({'result': 'PASS_INTEGRITY_ONLY', 'review_payloads': n, 'author_payloads': an,
                      'pinned_blobs': len(im['pinned_blobs']), 'primary_pdfs': len(im['primary_pdfs']),
                      'writes': 0, 'mathematics_certified_by_program': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as e:
        print('INTEGRITY_REJECT: ' + str(e))
        raise SystemExit(1)
