#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only verification of this review directory against an external
SHA256 anchor of manifest.json. Never reseals. Does not certify mathematics."""
import hashlib, json, os, re, stat, sys
from pathlib import Path


def sha(b):
    return hashlib.sha256(b).hexdigest()


def fail(msg):
    raise ValueError(msg)


def strict(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            fail('duplicate JSON key')
        out[k] = v
    return out


def check(anchor):
    if not re.fullmatch('[0-9a-f]{64}', anchor):
        fail('external SHA256 anchor required')
    root = Path(os.path.abspath(__file__)).parent
    for p in (root, *root.parents):
        if not stat.S_ISDIR(p.lstat().st_mode):
            fail('non-directory or symlink ancestor')
    files, dirs = {}, []

    def walk(d):
        for e in sorted(os.scandir(d), key=lambda e: e.name):
            q = Path(e.path)
            rel = q.relative_to(root).as_posix()
            s = q.lstat()
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel)
                walk(q)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    fail('hardlink: ' + rel)
                if q.name == 'manifest.json' and rel != 'manifest.json':
                    fail('nested manifest')
                b = q.read_bytes()
                files[rel] = {'bytes': len(b), 'sha256': sha(b)}
            else:
                fail('nonregular entry: ' + rel)

    walk(root)
    if 'manifest.json' not in files:
        fail('manifest missing')
    raw = (root / 'manifest.json').read_bytes()
    if sha(raw) != anchor:
        fail('external manifest anchor mismatch')
    manifest = json.loads(raw, object_pairs_hook=strict)
    if sorted(dirs) != manifest['directories']:
        fail('directory inventory mismatch')
    del files['manifest.json']
    if files != manifest['files']:
        fail('file inventory mismatch')
    for r in json.loads((root / 'primary-receipts.json').read_bytes(), object_pairs_hook=strict):
        b = (root / r['path']).read_bytes()
        if len(b) != r['bytes'] or sha(b) != r['sha256']:
            fail('primary identity mismatch: ' + r['path'])
    print(json.dumps({'status': 'PASS', 'files': len(files), 'directories': len(dirs)}))


if __name__ == '__main__':
    try:
        if len(sys.argv) != 2:
            fail('external SHA256 anchor required')
        check(sys.argv[1])
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
