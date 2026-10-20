#!/usr/bin/env python3
"""Contribution-review controls for T165P135. Read-only with respect to all inputs.

1. Recompute a whole-tree snapshot (type/mode/nlink/bytes/sha256) of the author root
   fresh-structural-discovery-r135 and diff it against the parent's original-snapshot.json.
2. Verify the three detached anchors and the scope/proof hashes against the brief values.
3. Copy the author root into this review root and run the author's read-only verifier
   plus sanity script on the copy, then confirm the copy is unchanged by them.
4. Recompute SHA-256 of the external dependencies listed in the parent replay.
Writes integrity-report.json into this review root. No writes anywhere else.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'discovery-structural-r135-parent'
PROJECT = HERE.parents[3]
AUTHOR = HERE.parent / 'fresh-structural-discovery-r135'
ANCHORS = {
    'FINAL.json': '9e01e0dbcdab7665d6ce58c904291cb3caeaef9e54f5befb023336abe21f6be6',
    'packet/MANIFEST.json': '6b997e3d8605220fc4845528d8213356c792e7d674eab50d7be9d16d4730eae5',
    'REPORT.md': '4ecc09d4de9fe7e2f5e095b7b0ac2215a6665438898378e6ee8c91de6b0e037e',
}
SCOPE = '1000a115e013b3bc28247fdc03f33b8d4ae3ee8ee2a41ce4da55c79e1081a99d'
PROOF = 'a12854336cc118cc9a49dd96bb72aeb142e618ab3466a2e1dc648ff77bf98f10'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root):
    out = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        rel = str(p.relative_to(root))
        if rel == '.':
            rel = '.'
        if stat.S_ISLNK(s.st_mode):
            out[rel] = {'type': 'symlink', 'target': os.readlink(p)}
        elif stat.S_ISDIR(s.st_mode):
            out[rel] = {'type': 'dir', 'mode': stat.S_IMODE(s.st_mode)}
        elif stat.S_ISREG(s.st_mode):
            out[rel] = {'type': 'file', 'mode': stat.S_IMODE(s.st_mode),
                        'nlink': s.st_nlink, 'bytes': s.st_size, 'sha256': sha(p)}
        else:
            raise AssertionError('special file: ' + str(p))
    return out


def main():
    report = {}
    before = snapshot(AUTHOR)
    parent_snap = json.loads((PARENT / 'original-snapshot.json').read_text())
    # parent snapshot keys: '.' for root dir; ours identical scheme
    report['author_root_matches_parent_snapshot'] = (before == parent_snap)
    if before != parent_snap:
        only_new = sorted(set(before) - set(parent_snap))
        only_old = sorted(set(parent_snap) - set(before))
        changed = sorted(k for k in set(before) & set(parent_snap) if before[k] != parent_snap[k])
        report['diff'] = {'only_now': only_new, 'only_parent': only_old, 'changed': changed}
    anchors_ok = {rel: (sha(AUTHOR / rel) == h) for rel, h in ANCHORS.items()}
    report['anchors_ok'] = anchors_ok
    report['scope_ok'] = sha(AUTHOR / 'packet/public/frozen-statement.md') == SCOPE
    report['proof_ok'] = sha(AUTHOR / 'packet/public/proof.md') == PROOF

    dependencies = ['AGENTS.md', 'sources/upstream.json', 'sources/preprints-tree.json',
        'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/research-brief-2026-10-20.txt',
        'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r135-brief.txt',
        'frontier/campaigns/2026-10-14/discovery-structural-r134-parent/disposition.md',
        'frontier/campaigns/2026-10-14/discovery-structural-r134-parent/contribution-r1-adoption/adoption.json',
        'frontier/campaigns/2026-10-14/t184i134-contribution-r1/packet/public/review.md',
        'frontier/campaigns/2026-10-14/t184i134-contribution-r1/packet/public/reading-limits.md',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/assessment.md',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/intake.json',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/task-status.json',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/substantive-handoff.json',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/replay.py',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/replay.json',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/original-snapshot.json',
        'frontier/campaigns/2026-10-14/discovery-structural-r135-parent/contribution-r1-brief.txt']
    parent_replay = json.loads((PARENT / 'replay.json').read_text())
    dep_report = {}
    for p in dependencies:
        cur = sha(PROJECT / p)
        rec = {'sha256_now': cur}
        if p in parent_replay['external_dependencies']:
            rec['matches_parent_replay'] = cur == parent_replay['external_dependencies'][p]
        dep_report[p] = rec
    report['external_dependencies'] = dep_report

    tree = json.loads((PROJECT / 'sources/preprints-tree.json').read_bytes())
    report['tree_entries'] = len(tree['tree'])
    report['tree_truncated'] = tree.get('truncated')
    report['tree_sha256_ok'] = sha(PROJECT / 'sources/preprints-tree.json') == \
        'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

    copy_root = HERE / 'scratch' / 'baseline-copy'
    if copy_root.exists():
        shutil.rmtree(copy_root)
    copy_root.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(AUTHOR, copy_root, symlinks=True)
    copy_before = snapshot(copy_root)
    proc = subprocess.run([sys.executable, '-B', str(copy_root / 'packet/public/verify.py'),
                           '--root', str(copy_root), '--project', str(PROJECT),
                           '--finalhash', ANCHORS['FINAL.json']],
                          capture_output=True, text=True, timeout=120)
    report['verifier'] = {'exit': proc.returncode, 'stdout': proc.stdout, 'stderr': proc.stderr}
    sanity = subprocess.run([sys.executable, '-B', str(copy_root / 'packet/public/sanity.py')],
                            capture_output=True, text=True, timeout=120, cwd=copy_root)
    report['sanity'] = {'exit': sanity.returncode, 'stdout': sanity.stdout,
                        'stderr': sanity.stderr}
    report['copied_input_unchanged'] = copy_before == snapshot(copy_root)
    report['author_root_unchanged_after_controls'] = before == snapshot(AUTHOR)
    (HERE / 'integrity-report.json').write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'external_dependencies'},
                     indent=1))


if __name__ == '__main__':
    main()
