#!/usr/bin/env python3
# MIT. Integrity only, not mathematical verification.
import hashlib, json, os, stat, sys
from pathlib import Path


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def real_directory_chain(root):
    # lstat before any resolution, so a symlinked root or ancestor is visible.
    for p in (root, *root.parents):
        if not stat.S_ISDIR(os.lstat(p).st_mode):
            raise ValueError('root/ancestor link or non-directory: ' + str(p))


def inventory(root):
    real_directory_chain(root)
    dirs, files = [], {}

    def walk(d):
        for p in sorted(d.iterdir()):
            st = os.lstat(p)
            rel = p.relative_to(root).as_posix()
            if stat.S_ISDIR(st.st_mode):
                dirs.append(rel)
                walk(p)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    raise ValueError('hardlink: ' + rel)
                if rel != 'manifest.json':
                    files[rel] = digest(p)
            else:
                raise ValueError('link/nonregular: ' + rel)

    walk(root)
    return {'directories': sorted(dirs), 'files': files}


def verify(root, anchor):
    real_directory_chain(root)
    manifest = root / 'manifest.json'
    st = os.lstat(manifest)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('manifest link/nonregular')
    if len(anchor) != 64 or digest(manifest) != anchor:
        raise ValueError('external anchor mismatch')
    if inventory(root) != json.loads(manifest.read_text()):
        raise ValueError('exact directory/file inventory mismatch')
    return len(json.loads(manifest.read_text())['files'])


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: verify.py ROOT EXTERNAL_MANIFEST_SHA256')
    try:
        n = verify(Path(sys.argv[1]).absolute(), sys.argv[2])
        print(f'PASS_INTEGRITY_ONLY files={n}')
    except Exception as e:
        raise SystemExit('REJECT: ' + str(e))
