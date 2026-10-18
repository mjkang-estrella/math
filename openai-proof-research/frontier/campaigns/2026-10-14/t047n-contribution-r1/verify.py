#!/usr/bin/env python3
"""Exact-inventory verifier for t047n-contribution-r1. MIT. Read-only; never reseals.

Trust requires external anchors for both manifest.json and this verifier.
Optionally rechecks the frozen author anchors relative to --repo.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

AUTHOR = {
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r29/manifest.json': 'c7eec0bc68f9bb04945e92187ac772fe5339de470745cecb04744db17d1d35cd',
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r29/verify.py': '609d25eb1ac648f93e5d430fbaf8a09daf19555c1283bb86e5f59ba94adcf880',
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r29/candidate-047.md': '8f68f16a99340c9cf3c83c4ae86386fdcfe2f907bf337afd7f303c7ad0910039',
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r29/scope-047.md': '12e3fb5941a068df0380710b8dcef236e313cdc22ed872ad372b3dab5dfcf181',
    'frontier/campaigns/2026-10-14/t047n-author-primary-clarification-r1/clarification.md': '354d3a2cb4007abbb8711689f4a89a89110ddd1535755632593df8b809cc1eba',
    'sources/preprints-tree.json': 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b',
}


def die(s): raise ValueError(s)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def no_link_ancestry(p):
    p = Path(os.path.abspath(p))
    for q in [p, *p.parents]:
        if stat.S_ISLNK(q.lstat().st_mode): die('symlink ancestry: ' + str(q))
    return p


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
    actual = {k: v for k, v in files.items() if k != 'manifest.json'}
    if actual != m['files']: die('exact file inventory/hash mismatch')
    if sorted(dirs) != sorted(m['directories']): die('exact directory inventory mismatch')
    checked = 0
    if a.repo:
        repo = no_link_ancestry(a.repo)
        for rel, h in AUTHOR.items():
            if digest(repo / rel) != h: die('author anchor mismatch: ' + rel)
            checked += 1
    print(json.dumps({'status': 'PASS', 'payloads': len(m['files']), 'directories': len(m['directories']),
                      'author_anchors_checked': checked}, sort_keys=True))


if __name__ == '__main__':
    try: main()
    except Exception as e:
        print('FAIL: ' + str(e), file=sys.stderr); sys.exit(1)
