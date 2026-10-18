#!/usr/bin/env python3
"""MIT. Verify the exact inventory of this review directory against an
externally reported manifest SHA256. Never writes or reseals anything.
Usage: verify.py EXTERNAL_MANIFEST_SHA256
"""
import hashlib, json, os, stat, sys
from pathlib import Path


def sha(b):
    return hashlib.sha256(b).hexdigest()


def check(expected):
    root = Path(os.path.abspath(__file__)).parent
    for p in (root, *root.parents):
        if not stat.S_ISDIR(p.lstat().st_mode):
            raise ValueError('non-directory or symlink ancestor')
    raw = (root / 'manifest.json').read_bytes()
    if sha(raw) != expected:
        raise ValueError('external manifest anchor mismatch')
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
    del files['manifest.json']
    m = json.loads(raw)
    if sorted(dirs) != m['directories']:
        raise ValueError('directory inventory mismatch')
    if files != m['files']:
        raise ValueError('file inventory mismatch')
    print(json.dumps({'status': 'PASS_EXACT_INVENTORY', 'files': len(files), 'directories': len(dirs)}))


if __name__ == '__main__':
    try:
        a = sys.argv[1] if len(sys.argv) == 2 else ''
        if len(a) != 64 or any(c not in '0123456789abcdef' for c in a):
            raise ValueError('external SHA256 argument required')
        check(a)
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
