#!/usr/bin/env python3
"""T133E proof-r1 review integrity replay (read-only).

Adapted from the campaign pattern in cm275-proof-r1/verify.py and the r75
author verify.py.  Certifies bytes and inventory only; it does not certify any
mathematics, contribution or eligibility.
"""
import argparse
import hashlib
import json
import os
import re
import stat
from pathlib import Path, PurePosixPath

AUTHOR_MANIFEST = '591ac5cc16fd39e64fb7e2c6f57ce2ea81c54a7f5003ef7e767dbfb2bd82dfa5'
AUTHOR_CANDIDATE = 'a5cebc35180338943c8a8bd330d2147875034a67a126f6bfeabf5c637425f49a'
AUTHOR_SCOPE = '3b7f81a5eccb420aec318e3bd26e1c72c9193b184cdb507ad350095c7797ba74'
SCHEMA = 'T133E-proof-review-r1-v1'
VERDICT = 'PASS_FULL_T133E'


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def unique(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key')
        out[k] = v
    return out


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
    files, dirs = set(), set()
    for folder, ds, fs in os.walk(root, followlinks=False):
        for n in ds + fs:
            p = Path(folder) / n
            r = name(p.relative_to(root).as_posix())
            st = p.lstat()
            need(not stat.S_ISLNK(st.st_mode), 'symlink: ' + r)
            if stat.S_ISDIR(st.st_mode):
                dirs.add(r)
            else:
                need(stat.S_ISREG(st.st_mode), 'nonregular: ' + r)
                need(st.st_nlink == 1, 'hardlink: ' + r)
                files.add(r)
    return files, dirs


def review(root, anchor):
    need(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'bad anchor')
    mp = root / 'review-manifest.json'
    need(not mp.is_symlink(), 'manifest symlink')
    data = mp.read_bytes()
    need(sha(data) == anchor, 'external anchor mismatch')
    m = parse(data)
    need(m.get('schema') == SCHEMA and m.get('verdict') == VERDICT, 'review schema')
    need(m.get('candidate_sha256') == AUTHOR_CANDIDATE and m.get('scope_sha256') == AUTHOR_SCOPE
         and m.get('author_manifest_sha256') == AUTHOR_MANIFEST, 'reviewed identity')
    files = {name(k): v for k, v in m['files'].items()}
    need('review-manifest.json' not in files, 'self-listed manifest')
    dirs = [name(d) for d in m['directories']]
    need(len(set(dirs)) == len(dirs), 'duplicate directory')
    fs, ds = inventory(root)
    need(fs == set(files) | {'review-manifest.json'}, 'file membership')
    need(ds == set(dirs), 'directory membership')
    for r, v in files.items():
        b = (root / r).read_bytes()
        need(sha(b) == v['sha256'] and len(b) == v['bytes'], 'payload hash: ' + r)
    return m, len(files)


def author(root, review_root):
    mp = root / 'MANIFEST.json'
    need(not mp.is_symlink(), 'author manifest symlink')
    data = mp.read_bytes()
    need(sha(data) == AUTHOR_MANIFEST, 'author manifest anchor')
    d = parse(data)
    fs, ds = inventory(root)
    need(fs == {name(k) for k in d} | {'MANIFEST.json'}, 'author file membership')
    expect_dirs = set()
    for k in d:
        expect_dirs.update(p.as_posix() for p in PurePosixPath(k).parents if p.as_posix() != '.')
    need(ds == expect_dirs, 'author directory membership')
    for k, v in d.items():
        b = (root / k).read_bytes()
        need(sha(b) == v['sha256'] and len(b) == v['bytes'], 'author payload: ' + k)
    need(sha((root / 'candidate.md').read_bytes()) == AUTHOR_CANDIDATE, 'author candidate')
    need(sha((root / 'scope-freeze.md').read_bytes()) == AUTHOR_SCOPE, 'author scope')
    for src, dst in [('MANIFEST.json', 'author-MANIFEST.json'), ('candidate.md', 'author-candidate.md'),
                     ('scope-freeze.md', 'author-scope-freeze.md')]:
        need((root / src).read_bytes() == (review_root / 'inputs' / dst).read_bytes(), 'snapshot drift: ' + dst)
    return len(d)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True, help='external SHA256 of review-manifest.json')
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--author-root', type=Path)
    a = ap.parse_args()
    root = a.root.absolute()
    aroot = (a.author_root or root.parent / 'fresh-structural-discovery-r75').absolute()
    m, n = review(root, a.anchor)
    an = author(aroot, root)
    print(json.dumps({'result': 'PASS_INTEGRITY_ONLY', 'review_payloads': n, 'author_payloads': an,
                      'verdict_recorded': m['verdict'], 'writes': 0,
                      'mathematics_certified_by_program': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as e:
        print('INTEGRITY_REJECT: ' + str(e))
        raise SystemExit(1)
