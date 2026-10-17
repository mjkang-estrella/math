#!/usr/bin/env python3
"""Read-only verifier for the OA057 proof review r1 package.

Integrity only: a passing run certifies exact bytes and membership, not
mathematics, novelty, or any campaign gate. Usage, from any directory:
    python3 -I -B verify.py --expected-manifest-sha256 <externally supplied hex>
"""
import argparse, hashlib, json, re, sys
from pathlib import Path

AUTHOR_ANCHORS = {
    'inventory.json': '30dab2f1f474a9644069b58eeead506968d8a495c3082c853d4d0988adc41451',
    'candidate.md': 'ac2aa7a43e1812c0e18053264512815f37b22ec5b15af0c7663cd93e0ca32954',
    'scope.json': '5b7d08ee2344828c1727ac8956f28b9e69f06ba2eafcc5f35fc69d6ec14a76e0',
    'reading-and-comparison.md': '975932e7a63be1cf998ed16a62449284cfa21d4cb4838c68de81168760296677',
    'verify_inventory.py': '81580cc82e9af0cac7ab6256ebd966bd11ec6dbdd6dc121a21f7e77e80ee0021',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256', required=True)
    ap.add_argument('--root', default=None, help='package directory (default: this file\'s directory)')
    ap.add_argument('--author-dir', default=None, help='author packet (default: ../fresh-arithmetic-discovery-r12)')
    ap.add_argument('--skip-author', action='store_true', help='only for relocated copies in controls')
    a = ap.parse_args()
    if not re.fullmatch('[0-9a-f]{64}', a.expected_manifest_sha256):
        raise SystemExit('FAIL: malformed external anchor')
    root = Path(a.root).resolve() if a.root else Path(__file__).resolve().parent
    mpath = root / 'manifest.json'
    if mpath.is_symlink() or not mpath.is_file():
        raise SystemExit('FAIL: manifest missing or link')
    raw = mpath.read_bytes()
    if sha(raw) != a.expected_manifest_sha256:
        raise SystemExit('FAIL: external anchor mismatch')  # checked before parsing
    man = json.loads(raw)
    seen = {}
    for p in sorted(root.rglob('*')):
        rel = p.relative_to(root).as_posix()
        if p.is_symlink():
            raise SystemExit('FAIL: link ' + rel)
        if p.is_dir():
            raise SystemExit('FAIL: unexpected directory ' + rel)
        if not p.is_file():
            raise SystemExit('FAIL: nonregular ' + rel)
        if rel == 'manifest.json':
            continue
        b = p.read_bytes()
        seen[rel] = {'bytes': len(b), 'sha256': sha(b)}
    if seen != man['files']:
        raise SystemExit('FAIL: exact membership/hash mismatch')
    if not a.skip_author:
        ad = Path(a.author_dir).resolve() if a.author_dir else root.parent / 'fresh-arithmetic-discovery-r12'
        for name, h in AUTHOR_ANCHORS.items():
            q = ad / name
            if q.is_symlink() or not q.is_file() or sha(q.read_bytes()) != h:
                raise SystemExit('FAIL: frozen author anchor changed: ' + name)
        if man.get('author_anchors') != AUTHOR_ANCHORS:
            raise SystemExit('FAIL: manifest author anchors differ')
    print(json.dumps({'status': 'PASS_INTEGRITY_ONLY', 'files': len(seen) + 1,
                      'proof_verdict_recorded': man.get('proof_verdict'),
                      'contribution_verdict': man.get('contribution_verdict'),
                      'certifies_mathematics': False}, sort_keys=True))


if __name__ == '__main__':
    main()
