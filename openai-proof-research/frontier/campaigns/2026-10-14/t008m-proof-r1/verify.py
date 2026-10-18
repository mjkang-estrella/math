#!/usr/bin/env python3
"""Exact inventory authentication of the T008M proof-review directory.
Integrity only, not a mathematical verdict.  Original code: MIT."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(msg):
    raise SystemExit('FAIL: ' + msg)


def no_dup(pairs):
    d = {}
    for k, v in pairs:
        if k in d:
            fail('duplicate JSON key')
        d[k] = v
    return d


def safe(rel):
    if not isinstance(rel, str) or not rel or rel.startswith('/') or '\\' in rel or \
            any(x in ('', '.', '..') for x in rel.split('/')):
        fail('unsafe path')


def root():
    # abspath does not resolve symlinks, so linked roots/ancestors are visible.
    script = Path(os.path.abspath(__file__))
    for p in [*reversed(script.parents), script]:
        st = os.lstat(p)
        if stat.S_ISLNK(st.st_mode):
            fail('root/ancestor/script symlink forbidden')
        if p != script and not stat.S_ISDIR(st.st_mode):
            fail('non-directory ancestor')
    return script.parent


def scan(base):
    files, dirs = set(), set()
    stack = [base]
    while stack:
        cur = stack.pop()
        for e in os.scandir(cur):
            q = Path(e.path)
            rel = q.relative_to(base).as_posix()
            safe(rel)
            st = os.lstat(q)
            if stat.S_ISLNK(st.st_mode):
                fail('symlink forbidden: ' + rel)
            elif stat.S_ISDIR(st.st_mode):
                dirs.add(rel)
                stack.append(q)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    fail('hardlink forbidden: ' + rel)
                files.add(rel)
            else:
                fail('nonregular object forbidden: ' + rel)
    return files, dirs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest-sha256', required=True)
    a = ap.parse_args()
    base = root()
    files, dirs = scan(base)
    mp = base / 'manifest.json'
    if 'manifest.json' not in files or sha(mp) != a.manifest_sha256:
        fail('wrong external manifest anchor')
    m = json.loads(mp.read_text(), object_pairs_hook=no_dup)
    if set(m) != {'schema', 'status', 'files', 'dirs'} or m['schema'] != 1 or \
            m['status'] != 'SEALED_PROOF_REVIEW_PASS_FULL_T008M':
        fail('manifest schema')
    if not isinstance(m['dirs'], list) or set(m['dirs']) != dirs or len(m['dirs']) != len(dirs):
        fail('directory inventory mismatch')
    rows = m['files']
    if not isinstance(rows, dict) or set(rows) != files - {'manifest.json'}:
        fail('file inventory mismatch')
    if 'verify.py' not in rows:
        fail('verifier not covered')
    for name, row in rows.items():
        safe(name)
        if not isinstance(row, dict) or set(row) != {'sha256', 'bytes'} or type(row['bytes']) is not int \
                or not re.fullmatch('[0-9a-f]{64}', str(row['sha256'])):
            fail('invalid row')
        p = base / name
        if p.stat().st_size != row['bytes'] or sha(p) != row['sha256']:
            fail('payload mismatch: ' + name)
    print(json.dumps({'status': 'PASS_INVENTORY_NOT_PROOF', 'files': len(rows) + 1, 'directories': len(dirs)}))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as e:
        fail(str(e))
