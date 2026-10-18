#!/usr/bin/env python3
"""MIT. Externally anchored exact-inventory verifier for the T025O54 proof-r1 review directory.
Adapted from t247g-proof-r1/verify.py (SHA256 7e627001fd9a5313d9034e041754ebbd4934ba9f7c41f6e9dfa1b592cf0ced2e);
only the author-packet table and labels changed.
Usage: verify.py EXTERNAL_MANIFEST_SHA256 [AUTHOR_PACKET_DIR]
The SHA256 of this directory's manifest.json must come from the parent's external record.
Optionally also checks the r54 author packet's seven dispatch-anchored files (read-only).
Never writes, never reseals; certifies bytes only, not mathematics.
"""
import hashlib, json, os, stat, sys
from pathlib import Path

AUTHOR = {
    'manifest.json': 'e32e49cd36807d4c18291bb60d45f6431e48fb0c61566bfcc6ca4f30a4c3ddd3',
    'scope-status.md': 'f6da553993dc03592a52711922035d412ca21b6840194fb4b3440e8e7415e0b6',
    'candidate-proof.md': '74217f39dd39087e9881c78048bf5ec1822218f4da997089feb36142265a9ef7',
    'constrained-descent.md': '4cdab2ae581fb42e4db335c41db32e797285c91fcf7669535e1900eded11a636',
    'contribution-comparison.md': '2282e8107869ac40d9393a328ab3f2ff64e85cb89f209ae02b65e80ca3adbac7',
    'reading-limits.md': 'a78dca74d4d00b5bd8c5bf3e803f90ec789e28ed751331a45a248568685cba43',
    'alternative-route.md': '829fe320bb5e293ee22325373b667fbcec9489f637491b07c31491c9e873e932',
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
