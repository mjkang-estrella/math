#!/usr/bin/env python3
"""MIT. Read-only identity verifier for t197h-proof-r1 against a REQUIRED external anchor."""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path


def sha(b):
    return hashlib.sha256(b).hexdigest()


def require(ok, why):
    if not ok:
        raise ValueError(why)


def check_ancestors(root):
    p = Path(os.path.abspath(root))
    for q in [p] + list(p.parents):
        require(not q.is_symlink(), 'symlink at root or ancestor: ' + str(q))


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
            files.append(rel)
        else:
            raise ValueError('symlink or nonregular node: ' + rel)

    walk(root, '.')
    return sorted(files), sorted(dirs)


def check(root, anchor):
    check_ancestors(root)
    root = Path(os.path.abspath(root))
    files, dirs = scan(root)
    raw = (root / 'MANIFEST.json').read_bytes()
    require(sha(raw) == anchor, 'external manifest anchor mismatch')
    m = json.loads(raw)
    names = [e['path'] for e in m['files']]
    require(len(names) == len(set(names)) and 'MANIFEST.json' not in names, 'invalid payload names')
    require(all(n and not n.startswith('/') and '..' not in n.split('/') for n in names), 'unsafe payload name')
    require(files == sorted(names + ['MANIFEST.json']), 'exact file inventory mismatch')
    require(dirs == m['directories'], 'exact directory inventory mismatch')
    for e in m['files']:
        b = (root / e['path']).read_bytes()
        require(len(b) == e['bytes'] and sha(b) == e['sha256'], 'payload mismatch: ' + e['path'])
    st = json.loads((root / 'status.json').read_text())
    require(st['verdict'] == 'PASS_FULL_T197H' and st['author_manifest_sha256'] ==
            '819bc0a77c9ae52ca8a1b2193f64fc2f84754c17b6d5e0750c0be0ae351fd8b2', 'status mismatch')
    return {'status': 'PASS', 'payload_files': len(names), 'directories': len(dirs),
            'scope': 'Identity only; not proof, novelty or contribution.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--root', type=Path)
    a = ap.parse_args()
    root = a.root if a.root else Path(os.path.abspath(__file__)).parent
    print(json.dumps(check(root, a.expected_manifest_sha256)))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:  # noqa: BLE001
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
