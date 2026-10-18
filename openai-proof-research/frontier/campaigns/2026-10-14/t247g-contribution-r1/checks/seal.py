#!/usr/bin/env python3
"""MIT. Write MANIFEST.json for an UNSEALED packet; refuses to overwrite."""
import argparse, hashlib, json, stat
from pathlib import Path


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', type=Path, required=True)
    root = p.parse_args().root.absolute()
    out = root / 'MANIFEST.json'
    if out.exists():
        raise SystemExit('refusing to overwrite existing MANIFEST.json')
    files, dirs = [], []

    def walk(q, rel):
        s = q.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for c in sorted(q.iterdir(), key=lambda x: x.name):
                walk(c, c.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode) and s.st_nlink == 1:
            b = q.read_bytes()
            files.append({'path': rel, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
        else:
            raise SystemExit('refusing nonregular or hardlinked node: ' + rel)

    walk(root, '.')
    m = {'packet': 'T247G contribution review r1', 'directories': sorted(dirs),
         'files': sorted(files, key=lambda e: e['path'])}
    out.write_text(json.dumps(m, indent=2) + '\n')
    print(hashlib.sha256(out.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
