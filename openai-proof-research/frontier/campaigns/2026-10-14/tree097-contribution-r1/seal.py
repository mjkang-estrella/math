#!/usr/bin/env python3
"""MIT. Write MANIFEST.json for a packet root and print its SHA256.

The printed hash must be recorded OUTSIDE the packet and passed to
verify.py; re-running this script after an edit produces a different
anchor and is not self-authorization.
"""
import hashlib, json, stat, sys
from pathlib import Path


def build(root):
    files, dirs = [], []

    def walk(p, rel):
        s = p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir(), key=lambda x: x.name):
                walk(q, q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            if s.st_nlink != 1:
                raise ValueError('hardlink: ' + rel)
            if rel != 'MANIFEST.json':
                b = p.read_bytes()
                files.append({'path': rel, 'bytes': len(b),
                              'sha256': hashlib.sha256(b).hexdigest()})
        else:
            raise ValueError('nonregular: ' + rel)

    walk(root, '.')
    m = {'packet': 'tree097-contribution-r1', 'verdict': 'TECHNICAL',
         'files': sorted(files, key=lambda e: e['path']), 'directories': sorted(dirs)}
    raw = (json.dumps(m, indent=1, sort_keys=True) + '\n').encode()
    (root / 'MANIFEST.json').write_bytes(raw)
    return hashlib.sha256(raw).hexdigest()


if __name__ == '__main__':
    root = Path(sys.argv[1]).absolute() if len(sys.argv) > 1 else Path(__file__).absolute().parent
    print(build(root))
