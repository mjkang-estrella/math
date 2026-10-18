#!/usr/bin/env python3
"""MIT. Verify this review directory against an externally reported manifest SHA256. Never reseals."""
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
        for entry in os.scandir(p):
            q = Path(entry.path)
            rel = q.relative_to(root).as_posix()
            s = q.lstat()
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if q.name == 'manifest.json' and rel != 'manifest.json':
                    raise ValueError('nested manifest')
                files[rel] = {'bytes': s.st_size, 'sha256': sha(q.read_bytes())}
            else:
                raise ValueError('nonregular entry: ' + rel)

    walk(root)
    manifest = json.loads(raw)
    del files['manifest.json']
    if sorted(dirs) != manifest['directories']:
        raise ValueError('directory inventory mismatch')
    if files != manifest['files']:
        raise ValueError('file inventory mismatch')
    print(json.dumps({'status': 'PASS', 'files': len(files), 'directories': len(dirs)}))


if __name__ == '__main__':
    try:
        if len(sys.argv) != 2 or len(sys.argv[1]) != 64:
            raise ValueError('external SHA256 argument required')
        check(sys.argv[1])
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
