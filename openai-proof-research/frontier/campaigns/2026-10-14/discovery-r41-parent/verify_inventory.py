#!/usr/bin/env python3
"""Parent byte-inventory check. No mathematical or contribution verdict."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, 'duplicate key')
        result[key] = value
    return result


def verify(root, anchor):
    root = root.absolute()
    for p in (root, *root.parents):
        need(stat.S_ISDIR(p.lstat().st_mode), 'non-directory or linked ancestor')
    files, dirs = {}, []

    def walk(path):
        for p in sorted(path.iterdir()):
            s = p.lstat()
            rel = p.relative_to(root).as_posix()
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                walk(p)
            else:
                need(stat.S_ISREG(s.st_mode), 'nonregular entry')
                need(s.st_nlink == 1, 'hardlink')
                files[rel] = hashlib.sha256(p.read_bytes()).hexdigest()
    walk(root)
    need(files.pop('manifest.json', None) == anchor, 'external anchor mismatch')
    m = json.loads((root / 'manifest.json').read_bytes(), object_pairs_hook=pairs)
    for name in m['files']:
        p = PurePosixPath(name)
        need(name not in ('', '.', 'manifest.json') and p.as_posix() == name
             and not p.is_absolute() and '..' not in p.parts and '\\' not in name,
             'unsafe member')
    need(files == m['files'], 'file inventory mismatch')
    need(sorted(dirs) == m['directories'], 'directory inventory mismatch')
    return dict(status='IDENTITY_ONLY', files=len(files), directories=len(dirs))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('root', type=Path)
    p.add_argument('--anchor', required=True)
    a = p.parse_args()
    try:
        print(json.dumps(verify(a.root, a.anchor)))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise SystemExit('REFUSED: ' + str(exc))
