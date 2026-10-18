#!/usr/bin/env python3
"""Exact-inventory verifier for the T337E proof-review r1 packet. MIT.

Read-only. Requires caller-supplied external SHA256 anchors for manifest.json
and for this verifier. Rejects parent traversal, root/ancestor/payload
symlinks, hardlinks, nonregular nodes, nested manifests, and any missing,
extra or changed file or directory. Uses explicit raises, so `python -O`
does not weaken any check.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path


class VerifyError(Exception):
    pass


def fail(msg):
    raise VerifyError(msg)


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def checked_path(raw):
    raw = os.fspath(raw)
    if '..' in Path(raw).parts:
        fail('parent traversal in path')
    p = Path(raw if os.path.isabs(raw) else os.path.join(os.getcwd(), raw))
    for q in [p, *p.parents]:
        if stat.S_ISLNK(q.lstat().st_mode):
            fail('symlink ancestry: ' + str(q))
    return p


def scan(root):
    files, dirs = {}, []

    def visit(d):
        for ent in sorted(os.scandir(d), key=lambda e: e.name):
            p = Path(ent.path)
            s = p.lstat()
            rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(s.st_mode):
                fail('symlink: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                visit(p)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    fail('hardlink: ' + rel)
                if p.name == 'manifest.json' and rel != 'manifest.json':
                    fail('nested manifest: ' + rel)
                files[rel] = {'bytes': s.st_size, 'sha256': digest(p)}
            else:
                fail('nonregular: ' + rel)

    visit(root)
    return files, dirs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root')
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    a = ap.parse_args()
    for h in (a.expected_manifest, a.expected_verifier):
        if len(h) != 64 or any(c not in '0123456789abcdef' for c in h):
            fail('anchor is not a lowercase SHA256 hex digest')
    script = checked_path(__file__)
    root = checked_path(a.root or script.parent)
    if digest(script) != a.expected_verifier:
        fail('executing verifier external anchor mismatch')
    if not root.is_dir():
        fail('root is not a directory')
    files, dirs = scan(root)
    if files.get('review-verify.py', {}).get('sha256') != a.expected_verifier:
        fail('packet verifier external anchor mismatch')
    if files.get('manifest.json', {}).get('sha256') != a.expected_manifest:
        fail('manifest external anchor mismatch')
    m = json.loads((root / 'manifest.json').read_text())
    actual = {k: v for k, v in files.items() if k != 'manifest.json'}
    if set(actual) != set(m['files']):
        fail('exact file inventory mismatch')
    if actual != m['files']:
        fail('file size/hash mismatch')
    if sorted(dirs) != sorted(m['directories']):
        fail('exact directory inventory mismatch')
    print(json.dumps({'status': 'PASS', 'payloads': len(m['files']),
                      'directories': len(m['directories'])}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
