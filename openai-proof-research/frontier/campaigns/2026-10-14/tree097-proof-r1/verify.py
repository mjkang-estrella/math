#!/usr/bin/env python3
"""MIT. Read-only verifier for the tree097-proof-r1 review packet.

Requires a caller-supplied external SHA256 of MANIFEST.json. Checks the exact
file and directory inventory and every payload's byte length and SHA256.
Rejects symlinks (including the root), hardlinked files, nested manifests and
any nonregular node. Certifies file identity only, not mathematics.
"""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path

HEX64 = re.compile(r'[0-9a-f]{64}')

def fail(why): raise ValueError(why)

def safe_rel(n):
    p = Path(n)
    return (isinstance(n, str) and n not in ('', '.') and not p.is_absolute()
            and '..' not in p.parts and p.as_posix() == n and '\\' not in n)

def scan(root):
    s = os.lstat(root)
    if not stat.S_ISDIR(s.st_mode): fail('root is not a real directory (symlink or other)')
    files, dirs = [], []
    def walk(p, rel):
        st = os.lstat(p)
        if stat.S_ISLNK(st.st_mode): fail('symlink: ' + rel)
        if stat.S_ISDIR(st.st_mode):
            dirs.append(rel)
            for name in sorted(os.listdir(p)):
                walk(p / name, name if rel == '.' else rel + '/' + name)
        elif stat.S_ISREG(st.st_mode):
            if st.st_nlink != 1: fail('hardlinked file: ' + rel)
            if p.name == 'MANIFEST.json' and rel != 'MANIFEST.json': fail('nested manifest: ' + rel)
            files.append(rel)
        else:
            fail('nonregular node: ' + rel)
    walk(root, '.')
    return sorted(files), sorted(dirs)

def check(root, anchor):
    if not HEX64.fullmatch(anchor or ''): fail('anchor must be 64 lowercase hex characters')
    files, dirs = scan(root)
    if 'MANIFEST.json' not in files: fail('missing MANIFEST.json')
    raw = (root / 'MANIFEST.json').read_bytes()
    if hashlib.sha256(raw).hexdigest() != anchor: fail('external manifest anchor mismatch')
    m = json.loads(raw)
    entries = m['files']; names = [e['path'] for e in entries]
    if len(names) != len(set(names)) or not all(safe_rel(n) and n != 'MANIFEST.json' for n in names):
        fail('invalid payload names')
    if files != sorted(names + ['MANIFEST.json']): fail('exact file inventory mismatch')
    if dirs != sorted(m['directories']) or len(set(m['directories'])) != len(m['directories']):
        fail('exact directory inventory mismatch')
    for e in entries:
        b = (root / e['path']).read_bytes()
        if len(b) != e['bytes'] or hashlib.sha256(b).hexdigest() != e['sha256']:
            fail('payload mismatch: ' + e['path'])
    return {'status': 'PASS', 'payload_files': len(entries), 'directories': len(dirs),
            'scope': 'Exact inventory and file identity only; not proof, contribution, or formal verification.'}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--root', type=Path)
    a = ap.parse_args()
    root = Path(os.path.abspath(a.root)) if a.root else Path(os.path.abspath(__file__)).parent
    print(json.dumps(check(root, a.expected_manifest_sha256)))

if __name__ == '__main__':
    try: main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
