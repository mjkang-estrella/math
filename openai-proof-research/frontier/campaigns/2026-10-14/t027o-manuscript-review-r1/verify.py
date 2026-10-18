#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only identity check of this review directory against a caller-supplied
external SHA256 of manifest.json. Never reseals. Does not certify mathematics.
Usage: verify.py --anchor SHA256"""
import hashlib, json, os, re, stat, sys
from pathlib import Path


class Reject(Exception):
    pass


def sha(b):
    return hashlib.sha256(b).hexdigest()


def strict(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise Reject('duplicate JSON key')
        out[k] = v
    return out


def check(anchor):
    if not re.fullmatch('[0-9a-f]{64}', anchor):
        raise Reject('external SHA256 anchor required')
    root = Path(os.path.abspath(__file__)).parent
    for p in (root, *root.parents):
        if not stat.S_ISDIR(p.lstat().st_mode):
            raise Reject('symlink ancestry')
    files, dirs = {}, []

    def walk(d):
        for e in sorted(os.scandir(d), key=lambda e: e.name):
            q = Path(e.path)
            rel = q.relative_to(root).as_posix()
            s = q.lstat()
            if stat.S_ISLNK(s.st_mode):
                raise Reject('symlink payload: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    raise Reject('hardlink: ' + rel)
                if q.name == 'manifest.json' and rel != 'manifest.json':
                    raise Reject('nested manifest')
                b = q.read_bytes()
                files[rel] = {'bytes': len(b), 'sha256': sha(b)}
            else:
                raise Reject('nonregular entry: ' + rel)

    walk(root)
    if 'manifest.json' not in files:
        raise Reject('manifest missing')
    raw = (root / 'manifest.json').read_bytes()
    if sha(raw) != anchor:
        raise Reject('external manifest anchor mismatch')
    manifest = json.loads(raw, object_pairs_hook=strict)
    del files['manifest.json']
    if sorted(dirs) != manifest['directories'] or files != manifest['files']:
        raise Reject('exact inventory mismatch')
    print(json.dumps({'result': 'PASS_REVIEW_IDENTITY_ONLY',
                      'verdict_recorded': manifest['verdict'],
                      'files': len(files), 'directories': len(dirs)}))


def main(argv):
    if len(argv) != 3 or argv[1] != '--anchor':
        raise Reject('external SHA256 anchor required')
    check(argv[2])


if __name__ == '__main__':
    try:
        main(sys.argv)
    except Reject as e:
        print('INTEGRITY_REJECT: ' + str(e), file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print('INTEGRITY_REJECT: malformed (' + type(e).__name__ + ')', file=sys.stderr)
        sys.exit(1)
