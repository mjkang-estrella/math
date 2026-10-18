#!/usr/bin/env python3
"""Read-only identity verifier for the T298P round-2 proof-review packet.

Usage: python3 -I -B verify.py [--anchor SHA256] [--root DIR]

Checks: MANIFEST.json SHA256 equals the external anchor (if given); the set
of regular files under the packet root, excluding MANIFEST.json, equals the
manifest file set exactly; each file is a regular, non-symlinked, single-link
file whose size and SHA256 match. Writes nothing. Identity only: no
mathematical verdict is recomputed.
"""
import hashlib, json, os, sys
from pathlib import Path


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def fail(msg):
    print('FAIL: ' + msg)
    sys.exit(1)


def main(argv):
    anchor, root = None, Path(__file__).resolve().parent
    i = 0
    while i < len(argv):
        if argv[i] == '--anchor':
            anchor = argv[i + 1]; i += 2
        elif argv[i] == '--root':
            root = Path(argv[i + 1]).resolve(); i += 2
        else:
            fail('usage')
    man_path = root / 'MANIFEST.json'
    if not man_path.is_file() or man_path.is_symlink():
        fail('manifest missing')
    if anchor is not None and sha(man_path) != anchor:
        fail('external manifest anchor')
    man = json.loads(man_path.read_text())
    listed = {e['path']: e for e in man['files']}
    present = set()
    for dirpath, dirnames, filenames in os.walk(root):
        for name in dirnames + filenames:
            p = Path(dirpath) / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                fail('symlink ' + rel)
            if p.is_dir():
                continue
            st = os.lstat(p)
            if not os.path.isfile(p) or st.st_nlink != 1:
                fail('nonregular or hardlinked ' + rel)
            if rel != 'MANIFEST.json':
                present.add(rel)
    if present != set(listed):
        fail('exact membership')
    for rel, e in sorted(listed.items()):
        p = root / rel
        if p.stat().st_size != e['size']:
            fail('size ' + rel)
        if sha(p) != e['sha256']:
            fail('sha256 ' + rel)
    print(json.dumps({'status': 'PASS', 'files': len(listed),
                      'verdict_recorded': man.get('verdict'),
                      'scope': 'identity only'}))


if __name__ == '__main__':
    main(sys.argv[1:])
