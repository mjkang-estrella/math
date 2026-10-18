#!/usr/bin/env python3
"""Read-only, externally anchored identity verifier for T298P contribution review r2.

It checks bytes and membership only. It gives no mathematical, contribution or
acceptance verdict. No writes, no network, no subprocesses.

Checks:
  1. sha256(MANIFEST.json) equals the externally reported --anchor.
  2. The review directory is flat: every entry is a regular, non-symlink file
     with link count 1, and the set equals the manifest files plus MANIFEST.json.
  3. Every manifest file matches its recorded byte length and sha256.
  4. Bound inputs: the author packet manifest anchor, the seven dispatched author
     anchors, the complete preprint tree anchor, the immutable source pin, and the
     six frozen round-1 draft files at their parent-captured hashes.
"""
import argparse
import hashlib
import json
import os
import stat
from pathlib import Path, PurePosixPath

AUTHOR_DIR = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r104'
R1_DIR = 'frontier/campaigns/2026-10-14/t298p-contribution-r1'
AUTHOR_ANCHORS = {
    'MANIFEST.json': 'b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3',
    'candidate.md': 'ed09eaca101d308384672977a8a9df9e37445c82f7d1fdabab528465ce158cb6',
    'scope-freeze.md': '8e9b3f5f30e02e91e8e49010350c07bb8dff845c806e506e8e5b598bed37589e',
    'comparison.md': '0316e9e94703ed7b809ed61c5a3aafc350d16ed8c250322882b7a197899084e3',
    'matched-volume-attempt.md': 'b8c4bd546975ff8ef9cc5eb7cb9baf0061ab9d427eacc342a9704ed7adf751cf',
    'unconditional-score-construction.md': '44da8c1da61422bb300058db6c0dbf7b8e87fe5dc913be348b77e45338c086fe',
    'stress-checks.md': 'aa0641aef28f00a9d7b9ce718e610f49c3789ebdcc57d2bdf0be1905b9655e18',
}
TREE_ANCHOR = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
R1_CAPTURED = {
    'verify.py': 'ea179ce8765b43f3d15fd03c855d3db80f9b2714dec036eea145d3d443493d7c',
    'checks.json': 'e980c210df37027642c7908b2d08493844bd77c274ed3cd15fcf7badde13ee42',
    'contribution-checks.json': '8ec7fe94b09620fc2b91a38c6f5cd6fbf9df92a9ea466cdb9323d654c234a159',
    'review.md': '83d3609e7cb8ba77cb7b432d9ad0f9dc50306c4285a209741a1c2358b0a4f6e7',
    'reading-limits.md': '0dec03ead9f51df699a0cb234492601ffb7bd7e2cdea8c7b579870da069a839f',
    'contribution-checks.py': '31f5960ae3dc8c58f6c5e9ad690d138bbbf22b7b91a134143eaf27e715a563f2',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def need(ok, reason):
    if not ok:
        raise SystemExit('FAIL: ' + reason)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--anchor', required=True)
    p.add_argument('--repo', required=True)
    a = p.parse_args()
    here = Path(__file__).resolve().parent
    repo = Path(a.repo).resolve()

    raw = (here / 'MANIFEST.json').read_bytes()
    need(sha(raw) == a.anchor, 'external manifest anchor')
    manifest = json.loads(raw)
    files = manifest['files']

    actual = set()
    for entry in os.scandir(here):
        st = os.lstat(entry.path)
        need(not stat.S_ISLNK(st.st_mode), 'symlink ' + entry.name)
        need(stat.S_ISREG(st.st_mode), 'non-regular entry ' + entry.name)
        need(st.st_nlink == 1, 'link count ' + entry.name)
        actual.add(entry.name)
    need(actual == set(files) | {'MANIFEST.json'}, 'exact membership')

    for name, row in files.items():
        path = PurePosixPath(name)
        need(len(path.parts) == 1 and not path.is_absolute() and name not in ('.', '..'),
             'flat manifest path ' + name)
        data = (here / name).read_bytes()
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'payload ' + name)

    author = repo / AUTHOR_DIR
    for name, h in AUTHOR_ANCHORS.items():
        need(sha((author / name).read_bytes()) == h, 'author anchor ' + name)
    need(sha((repo / 'sources/preprints-tree.json').read_bytes()) == TREE_ANCHOR, 'tree anchor')
    need(json.loads((repo / 'sources/upstream.json').read_text())['commit'] == PIN, 'source pin')
    r1 = repo / R1_DIR
    for name, h in R1_CAPTURED.items():
        need(sha((r1 / name).read_bytes()) == h, 'round-1 draft unchanged ' + name)

    print(json.dumps({
        'status': 'PASS',
        'payload_files': len(files),
        'author_anchors': len(AUTHOR_ANCHORS),
        'round1_files_unchanged': len(R1_CAPTURED),
        'scope': 'identity only; T298P contribution review r2; no mathematical, '
                 'contribution or acceptance verdict is checked',
    }, sort_keys=True))


if __name__ == '__main__':
    main()
