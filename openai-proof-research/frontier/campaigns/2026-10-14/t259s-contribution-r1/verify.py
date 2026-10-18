#!/usr/bin/env python3
"""Read-only exact-inventory verifier for the T259S contribution review r1. MIT.

Never writes or reseals. Anchors are supplied externally.
Optional --author-packet/--source-tree recompute the frozen author identities and compare
every copied source body to the canonical tree directly (no use of author receipts).
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

FROZEN = {
    'manifest.json': 'ff6bd1361506423bf135661e6d930e3635700f14db2de9471548afafc730454d',
    'verify.py': '245d3b949fa26a6ae42d214cef89c59a0d425ec8d366c746f69122e9b671d54d',
    'candidate-259.md': 'ee450dee9bd78fb4592313b9b30ac06dd41270019c59da318681423484912491',
    'scope-259.md': '50d98b466935720cfbf9d8f9764f7d8ad8a837a2e58480c7c6b7e44f5ea4f99d',
}
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FAMILY259 = 'A-group-without-fixed-price-October-5-2026'


def die(s):
    raise ValueError(s)


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def gitblob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def checked(raw):
    if '..' in os.fspath(raw).split(os.sep):
        die('parent traversal in path')
    p = Path(os.path.abspath(raw))
    for q in [p, *p.parents]:
        if stat.S_ISLNK(q.lstat().st_mode):
            die('symlink ancestry: ' + str(q))
    return p


def scan(root):
    files, dirs = {}, []

    def visit(d):
        for ent in sorted(os.scandir(d), key=lambda e: e.name):
            p = Path(ent.path); s = p.lstat(); rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(s.st_mode):
                die('symlink: ' + rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.append(rel); visit(p)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1:
                    die('hardlink: ' + rel)
                if p.name == 'manifest.json' and rel != 'manifest.json':
                    die('nested manifest')
                files[rel] = {'bytes': s.st_size, 'sha256': sha256(p)}
            else:
                die('nonregular: ' + rel)
    visit(root)
    return files, dirs


def author_check(packet, tree_path):
    packet = checked(packet); tree_path = checked(tree_path)
    for name, h in FROZEN.items():
        if sha256(packet / name) != h:
            die('frozen author identity mismatch: ' + name)
    if sha256(tree_path) != TREE_SHA256:
        die('canonical tree identity mismatch')
    tree = json.loads(tree_path.read_text())
    if tree.get('truncated') is not False:
        die('tree incomplete')
    entries = {x['path']: x for x in tree['tree'] if x['type'] == 'blob'}
    base = packet / 'private'
    copied = {}
    for d, _, fs in os.walk(base / 'preprints'):
        for f in fs:
            p = Path(d) / f
            copied[p.relative_to(base).as_posix()] = gitblob(p.read_bytes())
    for rel, g in copied.items():
        if rel not in entries or entries[rel]['sha'] != g:
            die('source body mismatch: ' + rel)
    fams = {r.split('/')[1] for r in copied}
    want = {p for p in entries if p.split('/')[1] in fams and not p.endswith('.pdf')}
    if set(copied) != want:
        die('source family completeness')
    fam259 = {p for p in entries if p.split('/')[1] == FAMILY259 and not p.endswith('.pdf')}
    if not fam259 <= set(copied):
        die('family259 incomplete')
    return len(copied), len(fam259)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root'); ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    ap.add_argument('--author-packet'); ap.add_argument('--source-tree')
    a = ap.parse_args()
    script = checked(__file__); root = checked(a.root or script.parent)
    if sha256(script) != a.expected_verifier:
        die('executing verifier external anchor mismatch')
    if not root.is_dir():
        die('root is not a directory')
    files, dirs = scan(root)
    if files.get('verify.py', {}).get('sha256') != a.expected_verifier:
        die('packet verifier external anchor mismatch')
    if files.get('manifest.json', {}).get('sha256') != a.expected_manifest:
        die('manifest external anchor mismatch')
    m = json.loads((root / 'manifest.json').read_text())
    if {k: v for k, v in files.items() if k != 'manifest.json'} != m['files']:
        die('exact file inventory/hash mismatch')
    if sorted(dirs) != sorted(m['directories']):
        die('exact directory inventory mismatch')
    out = {'status': 'PASS', 'payloads': len(m['files'])}
    if a.author_packet or a.source_tree:
        if not (a.author_packet and a.source_tree):
            die('--author-packet and --source-tree must be given together')
        out['author_source_blobs'], out['family259_nonpdf_blobs'] = author_check(a.author_packet, a.source_tree)
    print(json.dumps(out, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
