#!/usr/bin/env python3
"""Read-only externally anchored identity verifier for the T298P proof review r1.

Provenance: structure adapted from the author packet's verify.py
(fresh-structural-discovery-r104, SHA256 d02e8409...b6c3); rewritten by the
reviewer, adding regular-file/no-symlink checks and author-anchor binding.
Identity only: no mathematical verdict is computed here. Writes nothing.
"""
import argparse, hashlib, json, os, stat
from pathlib import Path

AUTHOR_ANCHORS = {
    "MANIFEST.json": "b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3",
    "candidate.md": "ed09eaca101d308384672977a8a9df9e37445c82f7d1fdabab528465ce158cb6",
    "scope-freeze.md": "8e9b3f5f30e02e91e8e49010350c07bb8dff845c806e506e8e5b598bed37589e",
    "comparison.md": "0316e9e94703ed7b809ed61c5a3aafc350d16ed8c250322882b7a197899084e3",
    "matched-volume-attempt.md": "b8c4bd546975ff8ef9cc5eb7cb9baf0061ab9d427eacc342a9704ed7adf751cf",
    "unconditional-score-construction.md": "44da8c1da61422bb300058db6c0dbf7b8e87fe5dc913be348b77e45338c086fe",
    "stress-checks.md": "aa0641aef28f00a9d7b9ce718e610f49c3789ebdcc57d2bdf0be1905b9655e18",
}

p = argparse.ArgumentParser()
p.add_argument('--anchor', required=True)
p.add_argument('--repo', required=True)
p.add_argument('--author-dir')
a = p.parse_args()
r = Path(__file__).resolve().parent
repo = Path(a.repo).resolve()
author = Path(a.author_dir).resolve() if a.author_dir else repo / 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r104'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def need(ok, reason):
    if not ok:
        raise SystemExit('FAIL: ' + reason)

m = r / 'MANIFEST.json'
need(m.is_file() and not m.is_symlink(), 'manifest regular file')
need(sha(m.read_bytes()) == a.anchor, 'external manifest anchor')
j = json.loads(m.read_text())
files = j['files']
for name in files:
    need(not Path(name).is_absolute() and '..' not in Path(name).parts, 'safe manifest path ' + name)
actual = set()
for root, dirs, fnames in os.walk(r, followlinks=False):
    for dname in dirs:
        need(not os.path.islink(os.path.join(root, dname)), 'no symlinked directory')
    for f in fnames:
        full = os.path.join(root, f)
        st = os.lstat(full)
        need(stat.S_ISREG(st.st_mode), 'regular file ' + os.path.relpath(full, r))
        actual.add(os.path.relpath(full, r))
need(actual == set(files) | {'MANIFEST.json'}, 'exact public membership')
for name, h in files.items():
    need(sha((r / name).read_bytes()) == h, 'payload ' + name)
for name, h in AUTHOR_ANCHORS.items():
    f = author / name
    need(f.is_file() and not f.is_symlink(), 'author file present ' + name)
    need(sha(f.read_bytes()) == h, 'author anchor ' + name)
need(j.get('author_manifest_anchor') == AUTHOR_ANCHORS['MANIFEST.json'], 'recorded author anchor')
need(j.get('verdict') == 'PASS_FULL_T298P', 'recorded verdict field')
print(json.dumps({'status': 'PASS', 'payload_files': len(files), 'author_anchors': len(AUTHOR_ANCHORS),
                  'scope': 'identity only; T298P proof review r1 packet; no mathematical verdict computed'}))
