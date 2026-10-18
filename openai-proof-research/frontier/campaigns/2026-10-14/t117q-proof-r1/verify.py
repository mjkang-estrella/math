#!/usr/bin/env python3
"""MIT. Read-only exact-inventory verifier for the T117Q proof-review packet.
Requires an externally supplied SHA256 of MANIFEST.json; the manifest is not its own anchor."""
import argparse, hashlib, json, stat, sys
from pathlib import Path

AUTHOR_ANCHOR = '053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def require(ok, why):
    if not ok:
        raise ValueError(why)


def safe(n):
    p = Path(n)
    return isinstance(n, str) and n not in ('', '.') and not p.is_absolute() and '..' not in p.parts and p.as_posix() == n


def scan(root):
    files, dirs = [], []
    def walk(p, rel):
        s = p.lstat()
        if stat.S_ISDIR(s.st_mode):
            dirs.append(rel)
            for q in sorted(p.iterdir(), key=lambda x: x.name):
                walk(q, q.relative_to(root).as_posix())
        elif stat.S_ISREG(s.st_mode):
            require(s.st_nlink == 1, 'hardlinked regular file: ' + rel)
            require(p.name != 'MANIFEST.json' or rel == 'MANIFEST.json', 'nested manifest: ' + rel)
            files.append(rel)
        else:
            raise ValueError('symlink or nonregular node: ' + rel)
    walk(root, '.')
    return sorted(files), sorted(dirs)


def check(root, anchor):
    files, dirs = scan(root)
    raw = (root / 'MANIFEST.json').read_bytes()
    require(sha(raw) == anchor, 'external manifest anchor mismatch')
    m = json.loads(raw)
    require(m.get('schema') == 'strict-exact-inventory-v1' and m.get('packet') == 't117q-proof-r1', 'manifest header mismatch')
    require(m.get('author_manifest_sha256') == AUTHOR_ANCHOR, 'author anchor binding mismatch')
    names = [e['path'] for e in m['files']]
    require(len(names) == len(set(names)) and all(safe(n) and n != 'MANIFEST.json' for n in names), 'invalid payload names')
    require(files == sorted(names + ['MANIFEST.json']), 'exact file inventory mismatch')
    require(dirs == sorted(m['directories']), 'exact directory inventory mismatch')
    for e in m['files']:
        b = (root / e['path']).read_bytes()
        require(len(b) == e['bytes'] and sha(b) == e['sha256'], 'payload mismatch: ' + e['path'])
    verdict = (root / 'review.md').read_text()
    require('**Verdict: PASS_FULL_T117Q.**' in verdict and '**Required objections: none.**' in verdict, 'verdict text mismatch')
    return {'status': 'PASS', 'payload_files': len(names), 'directories': len(dirs),
            'scope': 'Exact review-packet inventory only; not proof, novelty or acceptance evidence.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--root', type=Path)
    a = ap.parse_args()
    root = a.root.absolute() if a.root else Path(__file__).absolute().parent
    print(json.dumps(check(root, a.expected_manifest_sha256)))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
