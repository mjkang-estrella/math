#!/usr/bin/env python3
"""MIT. Read-only verification of the T197H contribution review against a REQUIRED caller-supplied anchor."""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path


def sha(b):
    return hashlib.sha256(b).hexdigest()


def require(ok, why):
    if not ok:
        raise ValueError(why)


def safe(n):
    return isinstance(n, str) and n not in ('', '.') and not Path(n).is_absolute() \
        and '..' not in Path(n).parts and Path(n).as_posix() == n


def ancestors_ok(root):
    # Reject the root or any ancestor that is a symlink or not a directory.
    p = Path(os.path.abspath(root))
    for q in [p] + list(p.parents):
        s = os.lstat(q)
        require(stat.S_ISDIR(s.st_mode) and not stat.S_ISLNK(s.st_mode), 'root or ancestor not a real directory: ' + str(q))
    require(os.path.realpath(p) == str(p), 'root path is not canonical')
    return p


def scan(root):
    files, dirs = [], []

    def walk(p, rel):
        s = p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir(), key=lambda x: x.name):
                walk(q, q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            require(s.st_nlink == 1, 'hardlinked regular file: ' + rel)
            require(p.name != 'MANIFEST.json' or rel == 'MANIFEST.json', 'nested manifest: ' + rel)
            files.append(rel)
        else:
            raise ValueError('symlink or nonregular node: ' + rel)
    walk(root, '.')
    return sorted(files), sorted(dirs)


def check(root, anchor):
    root = ancestors_ok(root)
    files, dirs = scan(root)
    raw = (root / 'MANIFEST.json').read_bytes()
    require(sha(raw) == anchor, 'external manifest anchor mismatch')
    m = json.loads(raw); entries = m['files']; names = [e['path'] for e in entries]
    require(len(names) == len(set(names)) and all(safe(n) and n != 'MANIFEST.json' for n in names), 'invalid payload names')
    require(files == sorted(names + ['MANIFEST.json']), 'exact file inventory mismatch')
    require(dirs == m['directories'], 'exact directory inventory mismatch')
    for e in entries:
        b = (root / e['path']).read_bytes()
        require(len(b) == e['bytes'] and sha(b) == e['sha256'], 'payload mismatch: ' + e['path'])
    return {'status': 'PASS', 'payload_files': len(entries), 'directories': len(dirs),
            'scope': 'Exact inventory and identities only; not proof, novelty or adoption.'}


def main():
    p = argparse.ArgumentParser(); p.add_argument('--expected-manifest-sha256', required=True); p.add_argument('--root')
    a = p.parse_args()
    root = a.root if a.root else os.path.dirname(os.path.abspath(__file__))
    print(json.dumps(check(root, a.expected_manifest_sha256)))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
