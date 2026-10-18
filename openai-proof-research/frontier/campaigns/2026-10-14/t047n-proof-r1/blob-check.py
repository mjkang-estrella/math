#!/usr/bin/env python3
"""Independent Git-blob comparison of the frozen packet's retained source bodies
against the complete canonical preprints tree. Does not read the packet receipts. MIT.

Usage: python3 -I blob-check.py PACKET_DIR PREPRINTS_TREE_JSON EXPECTED_TREE_SHA256
"""
import hashlib
import json
import sys
from pathlib import Path

FAMILIES = {
    'An-explicit-failure-of-complex-affine-space-cancellation-September-23-2026': 'source047',
    'A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026': 'companion',
    'An-explicit-noncoordinate-polynomial-with-affine-three-space-zero-fibre-September-24-2026': 'companion',
}


def gitblob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def main():
    packet, treepath, expected = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
    raw = treepath.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit('FAIL: tree anchor mismatch')
    tree = json.loads(raw)
    if tree.get('truncated') is not False:
        raise SystemExit('FAIL: tree truncated')
    blobs = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
    rows = []
    claimed_local = set()
    for fam, kind in FAMILIES.items():
        fam_paths = sorted(p for p in blobs if p.split('/')[1] == fam and not p.endswith('.pdf'))
        if not fam_paths:
            raise SystemExit('FAIL: family absent ' + fam)
        for p in fam_paths:
            if kind == 'source047':
                local = packet / 'private' / 'source047' / Path(p).name
            else:
                local = packet / 'private' / 'companions' / p
            if not local.is_file() or local.is_symlink():
                raise SystemExit('FAIL: missing local body for ' + p)
            g = gitblob(local.read_bytes())
            if g != blobs[p]:
                raise SystemExit('FAIL: blob mismatch ' + p)
            claimed_local.add(local.resolve())
            rows.append({'path': p, 'git_blob_sha1': g, 'local': str(local.relative_to(packet))})
    # no extra unexplained files in source047/companion private dirs
    for sub in ('private/source047', 'private/companions'):
        for f in (packet / sub).rglob('*'):
            if f.is_file() and f.resolve() not in claimed_local:
                raise SystemExit('FAIL: extra private body ' + str(f.relative_to(packet)))
    names047 = [Path(r['path']).name for r in rows if FAMILIES[r['path'].split('/')[1]] == 'source047']
    if len(names047) != len(set(names047)):
        raise SystemExit('FAIL: ambiguous source047 basename mapping')
    print(json.dumps({'status': 'PASS', 'tree_sha256': expected, 'matched_non_pdf_blobs': len(rows),
                      'by_family': {f: sum(1 for r in rows if r['path'].split('/')[1] == f) for f in FAMILIES},
                      'rows': rows}, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
