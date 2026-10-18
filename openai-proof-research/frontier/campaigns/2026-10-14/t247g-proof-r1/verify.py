#!/usr/bin/env python3
"""MIT. Externally anchored exact-inventory verifier for the T247G proof-r1 review directory.
Usage: verify.py EXTERNAL_MANIFEST_SHA256 [AUTHOR_PACKET_DIR]
The SHA256 of this directory's manifest.json must come from the parent's external record.
Optionally also checks the r61 author packet's nine named files against the fixed dispatch
hashes (read-only). Never writes, never reseals; certifies bytes only, not mathematics.
"""
import hashlib, json, os, stat, sys
from pathlib import Path

AUTHOR = {
    'MANIFEST.json': '38b748ab81407bdb6bbd6b8557fc9f4d27fc094884705e8fcd9963939c4907fd',
    'candidate.md': 'd15af71f00588d84ae95c8591139c1162dc4375439d60a020e183bbba8b36499',
    'original-scope.txt': '19e05d71ce3cf0478d81ddbf1cf3aacc2f089f07fc5ddbdb6ae8a9dbc1b930c3',
    'verify.py': '791fbd2cb2fdd0ffe6c90a283c47fefb9b5bea758d54cc817af89fdf8a56cae0',
    'primary-comparison.md': '9869d8eff84f9df1632b320fa75a54d2f63fbb5e5ef8a666ff4f39871c3e767b',
    'reading-limits.md': '4a1354476ed7530e0172351488829a7cfbe83767ef524e24044ceabbfe87e915',
    'tensor-mechanism.md': '2d608ca8535c79b97813589ecf364c67a5905f7b7a062dd32d339868aed774e8',
    'checkpoint.md': '40958cf8afd2c36cfb6d8d2504f1e2126677fc30287675f430d322ad3b488dc9',
    'formal-scope.md': 'c6b09192210de9273380327f70d9c23ed69c22144389b78a1b9a9351ab185af7',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def nolinks(p):
    for q in (p, *p.parents):
        if not stat.S_ISDIR(q.lstat().st_mode):
            raise ValueError('non-directory or symlink ancestor')


def check(expected, author=None):
    script = Path(sys.argv[0])
    if '..' in script.parts:
        raise ValueError('parent traversal in invocation')
    if not script.is_absolute():
        script = Path.cwd() / script
    root = script.parent
    nolinks(root)
    files, dirs = {}, []

    def walk(p):
        for e in os.scandir(p):
            q = Path(e.path); rel = q.relative_to(root).as_posix(); s = q.lstat()
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel); walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if q.name == 'manifest.json' and rel != 'manifest.json':
                    raise ValueError('nested manifest')
                files[rel] = {'bytes': s.st_size, 'sha256': sha(q.read_bytes())}
            else:
                raise ValueError('nonregular entry: ' + rel)
    walk(root)
    if 'manifest.json' not in files:
        raise ValueError('missing manifest')
    raw = (root / 'manifest.json').read_bytes()
    if sha(raw) != expected:
        raise ValueError('external manifest anchor mismatch')
    m = json.loads(raw)
    if sorted(dirs) != m['directories']:
        raise ValueError('directory inventory mismatch')
    del files['manifest.json']
    if files != m['files']:
        raise ValueError('file inventory mismatch')
    out = {'status': 'PASS_REVIEW_INVENTORY', 'files': len(files), 'directories': len(dirs),
           'verdict': m['verdict']}
    if author is not None:
        a = Path(author)
        if not a.is_absolute() or '..' in a.parts:
            raise ValueError('author packet path must be absolute')
        nolinks(a)
        for n, h in AUTHOR.items():
            q = a / n
            if not stat.S_ISREG(q.lstat().st_mode) or sha(q.read_bytes()) != h:
                raise ValueError('author packet mismatch: ' + n)
        out['author_packet'] = 'PASS_DISPATCH_HASHES'
    print(json.dumps(out))


if __name__ == '__main__':
    try:
        if len(sys.argv) not in (2, 3) or len(sys.argv[1]) != 64 or any(c not in '0123456789abcdef' for c in sys.argv[1]):
            raise ValueError('external SHA256 argument required')
        check(sys.argv[1], sys.argv[2] if len(sys.argv) == 3 else None)
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
