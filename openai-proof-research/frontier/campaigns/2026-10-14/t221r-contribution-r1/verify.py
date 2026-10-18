#!/usr/bin/env python3
"""Exact-inventory verifier for t221r-contribution-r1. MIT. Read-only; never reseals.

Trust requires external anchors for both manifest.json and this verifier;
both are checked before the manifest is parsed. With --repo it also rechecks
the frozen author anchors and the canonical family-221 Git-blob inventory.
Byte identity only; never a theorem or contribution conclusion.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path, PurePosixPath

PKT = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r44/'
AUTHOR = {
    PKT + 'manifest.json': 'c288940c8c88f67a7374d998a7c49d822f64000abb981517303f1bf4af9739c6',
    PKT + 'verify.py': '22bc163b277aa160698b01a7d3a4104e3025c7a17cdd51274ddbbb59f2c38b82',
    PKT + 'controls.py': '93425bee00ffa83114837541a0961c7adc7c6dd7c24781b6f17c226539d51583',
    PKT + 'proof.md': 'c2d6631489bc3e2c31dfd2eb986a1987ff477b55c3a837556e3a0923a67fefa0',
    PKT + 'original-scope.txt': '26312b8fd6fb6a4bacb27085f0b46b760cc8f884754bed03e937c1b40328693c',
    PKT + 'reading-and-comparison.md': '11d63dd5cfbf1a6b63a0fdbcadc7dda31a4f0c933c0ea3462d4843678ddebc1d',
    'sources/preprints-tree.json': 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b',
}
FAM221 = 'preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/'
FAM221_FILES = 16


def die(s): raise ValueError(s)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def gitblob(b): return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def no_link_ancestry(p):
    p = Path(os.path.abspath(p))
    for q in [p, *p.parents]:
        if stat.S_ISLNK(q.lstat().st_mode): die('symlink ancestry: ' + str(q))
    return p


def safe(name):
    p = PurePosixPath(name)
    return (isinstance(name, str) and name and not p.is_absolute() and '\\' not in name
            and all(x not in ('', '.', '..') for x in name.split('/')) and str(p) == name)


def scan(root):
    files, dirs = {}, []
    def visit(d):
        for e in sorted(os.scandir(d), key=lambda e: e.name):
            p = Path(e.path); s = p.lstat(); rel = p.relative_to(root).as_posix()
            if stat.S_ISLNK(s.st_mode): die('symlink: ' + rel)
            if stat.S_ISDIR(s.st_mode): dirs.append(rel); visit(p)
            elif stat.S_ISREG(s.st_mode):
                if s.st_nlink != 1: die('hardlink: ' + rel)
                if p.name == 'manifest.json' and rel != 'manifest.json': die('nested manifest')
                files[rel] = {'bytes': s.st_size, 'sha256': digest(p)}
            else: die('nonregular: ' + rel)
    visit(root)
    return files, dirs


def family221(repo):
    tree = json.loads((repo / 'sources/preprints-tree.json').read_text())
    if tree.get('truncated') is not False: die('pinned tree incomplete')
    canon = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob' and x['path'].startswith(FAM221)}
    base = repo / PKT / 'private'
    local = set()
    for dp, dn, fn in os.walk(base / FAM221):
        for f in fn: local.add((Path(dp) / f).relative_to(base).as_posix())
    if local - set(canon): die('extra family-221 local files')
    if {k for k in canon if not k.endswith('.pdf')} != local: die('family-221 inventory mismatch')
    for k in sorted(local):
        q = base / k
        if not stat.S_ISREG(q.lstat().st_mode): die('family-221 nonregular: ' + k)
        if gitblob(q.read_bytes()) != canon[k]: die('family-221 blob mismatch: ' + k)
    if len(local) != FAM221_FILES: die('family-221 count mismatch')
    return len(local)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest', required=True)
    ap.add_argument('--expected-verifier', required=True)
    ap.add_argument('--repo')
    a = ap.parse_args()
    script = no_link_ancestry(__file__); root = script.parent
    if digest(script) != a.expected_verifier: die('executing verifier external anchor mismatch')
    files, dirs = scan(root)
    if files.get('manifest.json', {}).get('sha256') != a.expected_manifest: die('manifest external anchor mismatch')
    if files.get('verify.py', {}).get('sha256') != a.expected_verifier: die('packet verifier external anchor mismatch')
    m = json.loads((root / 'manifest.json').read_text())
    if not isinstance(m.get('files'), dict) or not isinstance(m.get('directories'), list): die('manifest schema')
    names = list(m['files']) + m['directories']
    if len(names) != len(set(names)) or not all(safe(n) for n in names) or 'manifest.json' in names:
        die('unsafe or duplicate manifest path')
    actual = {k: v for k, v in files.items() if k != 'manifest.json'}
    if actual != m['files']: die('exact file inventory/hash mismatch')
    if sorted(dirs) != sorted(m['directories']): die('exact directory inventory mismatch')
    checked = fam = 0
    if a.repo:
        repo = no_link_ancestry(a.repo)
        for rel, h in AUTHOR.items():
            p = repo / rel
            if not stat.S_ISREG(p.lstat().st_mode) or digest(p) != h: die('author anchor mismatch: ' + rel)
            checked += 1
        fam = family221(repo)
    print(json.dumps({'status': 'PASS_IDENTITY_ONLY', 'payloads': len(m['files']),
                      'directories': len(m['directories']), 'author_anchors_checked': checked,
                      'family221_blobs_checked': fam, 'verdict_recorded': m.get('verdict')}, sort_keys=True))


if __name__ == '__main__':
    try: main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
