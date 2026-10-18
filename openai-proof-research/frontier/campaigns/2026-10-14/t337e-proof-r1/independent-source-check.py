#!/usr/bin/env python3
"""Independent source-identity check for the T337E author packet. MIT.

Read-only. Does not use the author's receipts or bindings. Each copied source
body is hashed as a Git blob and compared with the path obtained from a fixed
directory prefix in the research repository's canonical
sources/preprints-tree.json (not the packet copy, not the truncated tree.json).
Identity checking is not mathematical evidence.

usage: independent-source-check.py RESEARCH_ROOT PACKET_DIR
"""
import hashlib, json, sys
from pathlib import Path

PREFIX = {
    'private/source337/': 'preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/',
    'private/smooth337/': 'preprints/Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/',
    'private/source081/': 'preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/',
}
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'


def git_blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


def main(research, packet):
    tree_path = research / 'sources/preprints-tree.json'
    raw = tree_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != TREE_SHA256:
        raise SystemExit('REJECT: canonical tree hash mismatch')
    tree = json.loads(raw)
    if tree['truncated'] is not False:
        raise SystemExit('REJECT: truncated tree')
    blobs = {r['path']: r['sha'] for r in tree['tree'] if r['type'] == 'blob'}
    copied_tree = packet / 'private/context/sources/preprints-tree.json'
    report = {'canonical_tree_sha256': TREE_SHA256, 'tree_entries': len(tree['tree']),
              'packet_tree_copy_identical': copied_tree.read_bytes() == raw, 'families': {}}
    total = 0
    for local, remote in PREFIX.items():
        base = packet / local
        matched, missing_locally = [], []
        for p in sorted(base.rglob('*')):
            if not p.is_file():
                continue
            rel = p.relative_to(base).as_posix()
            sha = blobs.get(remote + rel)
            if sha is None:
                raise SystemExit('REJECT: no canonical path for ' + local + rel)
            if git_blob(p.read_bytes()) != sha:
                raise SystemExit('REJECT: blob mismatch for ' + local + rel)
            matched.append(rel)
        for path in blobs:
            if path.startswith(remote) and path[len(remote):] not in matched:
                missing_locally.append(path[len(remote):])
        total += len(matched)
        report['families'][local] = {'matched': len(matched),
                                     'canonical_paths_not_copied': sorted(missing_locally)}
    for name in ['AGENTS.md', 'sources/upstream.json', 'sources/CONTENTS.md']:
        report.setdefault('context_copies_identical', {})[name] = \
            (packet / 'private/context' / name).read_bytes() == (research / name).read_bytes()
    report['total_matched'] = total
    report['status'] = 'PASS_IDENTITY_ONLY'
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    main(Path(sys.argv[1]).absolute(), Path(sys.argv[2]).absolute())
