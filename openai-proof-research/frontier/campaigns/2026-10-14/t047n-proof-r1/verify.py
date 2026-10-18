#!/usr/bin/env python3
"""External-anchor exact-inventory verifier for the T047N proof review r1. MIT.
Read-only: never writes or reseals.

Usage: python3 -I verify.py --expected-manifest SHA256 --expected-verifier SHA256 [--root DIR]
"""
import argparse
import hashlib
import json
import os
import stat
import sys
from pathlib import Path


def die(msg):
    raise ValueError(msg)


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def no_symlink_ancestry(p):
    p = Path(os.path.abspath(p))
    for q in [p, *p.parents]:
        if stat.S_ISLNK(q.lstat().st_mode):
            die('symlink in root or ancestry: ' + str(q))
    return p


def scan(root):
    files, dirs = {}, []

    def visit(d):
        for ent in sorted(os.scandir(d), key=lambda e: e.name):
            p = Path(ent.path)
            st = p.lstat()
            rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(st.st_mode):
                die('symlink: ' + rel)
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
                visit(p)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    die('hardlink: ' + rel)
                if p.name == 'manifest.json' and rel != 'manifest.json':
                    die('nested manifest: ' + rel)
                files[rel] = {'bytes': st.st_size, 'sha256': digest(p)}
            else:
                die('nonregular node: ' + rel)
    visit(root)
    return files, dirs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    ap.add_argument('--root')
    a = ap.parse_args()
    script = no_symlink_ancestry(__file__)
    root = no_symlink_ancestry(a.root or script.parent)
    if digest(script) != a.expected_verifier:
        die('executing verifier external anchor mismatch')
    if not root.is_dir():
        die('root is not a directory')
    files, dirs = scan(root)
    if files.get('verify.py', {}).get('sha256') != a.expected_verifier:
        die('packet verifier external anchor mismatch')
    if files.get('manifest.json', {}).get('sha256') != a.expected_manifest:
        die('manifest external anchor mismatch')
    m = json.loads((root / 'manifest.json').read_text())
    actual = {k: v for k, v in files.items() if k != 'manifest.json'}
    if actual != m['files']:
        die('exact file inventory/hash mismatch')
    if sorted(dirs) != sorted(m['directories']):
        die('exact directory inventory mismatch')
    print(json.dumps({'status': 'PASS', 'files': len(actual), 'directories': len(dirs),
                      'limit': 'Identity evidence only; certifies no theorem.'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
