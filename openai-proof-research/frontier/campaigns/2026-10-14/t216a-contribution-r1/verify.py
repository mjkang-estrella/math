#!/usr/bin/env python3
# MIT. Integrity only: certifies byte identity and exact membership, no mathematics.
import hashlib, json, os, stat, sys
from pathlib import Path

MANIFEST = 'manifest.json'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def real_directory_chain(root):
    # lstat before any resolution: resolving would hide a symlinked root or ancestor.
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
                if rel != MANIFEST:
                    files[rel] = digest(p)
            else:
                raise ValueError('link/nonregular: ' + rel)

    walk(root)
    return {'directories': sorted(dirs), 'files': files}


def verify(root, anchor):
    real_directory_chain(root)
    m = root / MANIFEST
    st = os.lstat(m)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise ValueError('manifest link/nonregular/hardlink')
    if len(anchor) != 64 or digest(m) != anchor:
        raise ValueError('external anchor mismatch')
    expected = json.loads(m.read_text())
    if inventory(root) != expected:
        raise ValueError('exact directory/file inventory mismatch')
    return len(expected['files']), len(expected['directories'])


def verify_author(author_root, record):
    # Optional observation of the frozen author packet's externally supplied anchors.
    real_directory_chain(author_root)
    for name, h in json.loads(record.read_text())['observed_author_files_sha256'].items():
        p = author_root / name
        st = os.lstat(p)
        if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1 or digest(p) != h:
            raise ValueError('author file mismatch: ' + name)


if __name__ == '__main__':
    args = sys.argv[1:]
    if len(args) not in (2, 4) or (len(args) == 4 and args[2] != '--author'):
        raise SystemExit('usage: verify.py ROOT EXTERNAL_MANIFEST_SHA256 [--author AUTHOR_ROOT]')
    try:
        root = Path(args[0]).absolute()
        n, d = verify(root, args[1])
        msg = f'PASS_INTEGRITY_ONLY files={n} directories={d}'
        if len(args) == 4:
            verify_author(Path(args[3]).absolute(), root / 'author-verification.json')
            msg += ' author_anchors=8'
        print(msg)
    except Exception as e:
        raise SystemExit('REJECT: ' + str(e))
