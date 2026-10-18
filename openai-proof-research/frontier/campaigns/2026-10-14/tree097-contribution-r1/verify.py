#!/usr/bin/env python3
"""MIT. Read-only integrity check of this review packet.

The manifest anchor MUST be supplied by the caller from an external record;
the packet never certifies its own manifest. Identity only: this does not
verify mathematics, novelty or the review verdict.
"""
import argparse, hashlib, json, stat, sys
from pathlib import Path

AUTHOR_ANCHORS = {
    'MANIFEST.json': 'ceb4d164b90d6ed3c81ba0338e120b5ee641cf7a46e9f2a18b8e7fa2c25e572e',
    'candidate.md': '7035c4b5216ac37610132045608041110722980c6546746491803e52c21889a8',
    'original-scope.txt': '08338d40a730c126691accaaa60db530116b5df44393ca22d2c1663cc9099821',
    'prefix-law.md': 'baa4071a53f0c80e8af9be3f8179e877220497317cd2f24c73f7ee74ab1ac8ee',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def require(ok, why):
    if not ok:
        raise ValueError(why)


def safe(n):
    p = Path(n)
    return (isinstance(n, str) and n not in ('', '.') and not p.is_absolute()
            and '..' not in p.parts and p.as_posix() == n)


def scan(root):
    files, dirs = [], []
    rs = root.lstat()
    require(stat.S_ISDIR(rs.st_mode), 'root is not a real directory')

    def walk(p, rel):
        s = p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir(), key=lambda x: x.name):
                walk(q, q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            require(s.st_nlink == 1, 'hardlinked file: ' + rel)
            files.append(rel)
        else:
            raise ValueError('symlink or nonregular node: ' + rel)

    walk(root, '.')
    return sorted(files), sorted(dirs)


def check(root, anchor):
    require(isinstance(anchor, str) and len(anchor) == 64
            and all(c in '0123456789abcdef' for c in anchor), 'malformed anchor')
    files, dirs = scan(root)
    require('MANIFEST.json' in files, 'missing MANIFEST.json')
    raw = (root / 'MANIFEST.json').read_bytes()
    require(sha(raw) == anchor, 'external manifest anchor mismatch')
    m = json.loads(raw)
    entries = m['files']
    names = [e['path'] for e in entries]
    require(len(names) == len(set(names)), 'duplicate manifest entries')
    require(all(safe(n) and n != 'MANIFEST.json' for n in names), 'invalid payload names')
    require(files == sorted(names + ['MANIFEST.json']), 'exact file inventory mismatch')
    require(all(safe(d) or d == '.' for d in m['directories']), 'invalid directory names')
    require(dirs == sorted(m['directories']), 'exact directory inventory mismatch')
    for e in entries:
        b = (root / e['path']).read_bytes()
        require(len(b) == e['bytes'] and sha(b) == e['sha256'], 'payload mismatch: ' + e['path'])
    return {'status': 'PASS', 'payload_files': len(entries), 'directories': len(dirs),
            'scope': 'Exact file/directory inventory and payload identity only; '
                     'not proof, novelty or verdict certification.'}


def check_author(author_root):
    for name, h in AUTHOR_ANCHORS.items():
        p = author_root / name
        require(stat.S_ISREG(p.lstat().st_mode), 'author file not regular: ' + name)
        require(sha(p.read_bytes()) == h, 'frozen author file changed: ' + name)
    return {'author_frozen_files': 'PASS', 'count': len(AUTHOR_ANCHORS)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--root', type=Path)
    ap.add_argument('--author-root', type=Path,
                    help='optional read-only check of the frozen r44 anchors')
    a = ap.parse_args()
    root = a.root.absolute() if a.root else Path(__file__).absolute().parent
    out = check(root, a.expected_manifest_sha256)
    if a.author_root:
        out.update(check_author(a.author_root.absolute()))
    print(json.dumps(out))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
