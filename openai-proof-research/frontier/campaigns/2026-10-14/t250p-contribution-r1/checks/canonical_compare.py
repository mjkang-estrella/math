#!/usr/bin/env python3
"""MIT. Read-only identity replay for the frozen T250P author packet.

Checks the five externally supplied anchors before any manifest parsing, then
compares every selected source body in the packet against the separately
anchored canonical sources/preprints-tree.json (not against the packet's own
copied inventory). Identity only: proves no mathematics.
"""
import hashlib, json, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
PACKET = REPO / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r35'
TREE = REPO / 'sources/preprints-tree.json'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
ANCHORS = {
    'manifest.json': '90c944f17915ef689c69139cda49b2b95f9174c1a84c1a2e4c70da7dc84d821d',
    'verify.py': 'f7e05e5fa0b20112065ab039935144922edd6975e40021e8121214ed7eaf4d89',
    'candidate250p.md': '92f999bdc7439b182e4fca752b017910d766c7c577cffa97cfb4afa2d54b4047',
    'scope250p.md': '79fd4364beb017caf43d976936632bb0fdefc41e83bbbcaa3bc35c7309daf72b',
    'source-and-credit.md': '5d5eb86d698502d1c8149183fb1dd0f845879d2ae99cc41f5b3b60be4cb46520',
}
FAMILIES = [
    'preprints/A-universal-group-of-type-F-infinity-September-23-2026',
    'preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026',
    'preprints/Simple-F-infinity-overgroups-of-groups-with-decidable-word-problem-September-23-2026',
]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b'blob %d\0' % len(b) + b).hexdigest()


def main():
    out = {'anchors': {}}
    for name, want in ANCHORS.items():
        got = sha((PACKET / name).read_bytes())
        out['anchors'][name] = got == want
        if got != want:
            raise SystemExit('FAIL: external anchor mismatch for ' + name)
    raw_tree = TREE.read_bytes()
    if sha(raw_tree) != TREE_SHA256:
        raise SystemExit('FAIL: canonical tree anchor mismatch')
    tree = json.loads(raw_tree)
    entries = tree['tree']
    if len(entries) != 13223 or tree['truncated'] is not False:
        raise SystemExit('FAIL: canonical tree is not the complete 13223-entry listing')
    canon = {e['path']: e for e in entries}
    receipts = json.loads((PACKET / 'source250-receipts.json').read_text())
    mismatches = []
    for r in receipts:
        b = (PACKET / r['path']).read_bytes()
        e = canon.get(r['source_path'])
        if e is None or e['type'] != 'blob' or e['sha'] != git_blob(b):
            mismatches.append(r['source_path'])
        if r['path'] != 'private/' + r['source_path']:
            mismatches.append('path-mapping:' + r['path'])
    have = {r['source_path'] for r in receipts}
    families = {}
    for d in FAMILIES:
        blobs = sorted(p for p, e in canon.items() if p.startswith(d + '/') and e['type'] == 'blob')
        nonpdf = [p for p in blobs if not p.lower().endswith('.pdf')]
        families[d] = {'canonical_blobs': len(blobs), 'non_pdf': len(nonpdf),
                       'missing_from_packet': [p for p in nonpdf if p not in have],
                       'pdf_not_retrieved': [p for p in blobs if p.lower().endswith('.pdf')]}
    extra = sorted(p for p in have if not any(p.startswith(d + '/') for d in FAMILIES))
    inv = json.loads((PACKET / 'source-family-inventory.json').read_text())
    inv_diffs = [e['path'] for e in inv['entries']
                 if canon.get(e['path'], {}).get('sha') != e.get('sha')
                 or canon.get(e['path'], {}).get('type') != e.get('type')]
    ok = not mismatches and not extra and not inv_diffs and all(
        not f['missing_from_packet'] for f in families.values())
    out.update({
        'status': 'PASS' if ok else 'FAIL',
        'canonical_tree_sha256': TREE_SHA256, 'canonical_entries': len(entries),
        'canonical_truncated': tree['truncated'], 'canonical_tree_object': tree['sha'],
        'selected_source_blobs': len(receipts), 'byte_mismatches': mismatches,
        'selected_outside_families': extra, 'families': families,
        'copied_inventory_entries': len(inv['entries']), 'copied_inventory_diffs': inv_diffs,
        'scope': 'Identity only. The copied inventory is checked against the canonical tree, not trusted.',
    })
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
