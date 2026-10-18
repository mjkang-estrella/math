#!/usr/bin/env python3
"""Read-only external-anchor integrity verifier for the T338N contribution
review r1 directory. Integrity only; no mathematical content is certified.

Adapted from the author packet's verify.py (fresh-analytic-discovery-r89,
sha256 902bd1800db5ad02e04c2efc9a0ac2afd632ea2400f8db5f5c7a75a81a002997):
same external-anchor, exact-membership and link-rejection design. Changes:
review-specific status fields, and rejection of symlinks/nonregular files
anywhere in the tree walk, not only at payload positions. This script never
writes, downloads, stages, or modifies anything; it only reads."""
import argparse, hashlib, json, os, pathlib, sys

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--manifest-sha256', required=True)
    a = ap.parse_args()
    b = pathlib.Path(__file__).resolve().parent
    m = b / 'MANIFEST.json'
    require(m.is_file() and not m.is_symlink(), 'manifest missing or unsafe')
    require(digest(m) == a.manifest_sha256, 'external manifest anchor mismatch')
    j = json.loads(m.read_text())
    require(j.get('review_role') == 'contribution', 'wrong review role')
    require(j.get('verdict') == 'TECHNICAL', 'verdict field mismatch')
    require(j.get('accepted') is False and j.get('count_change') == 0,
            'invalid acceptance status')
    require(j.get('correctness_gate') == 'SEPARATE_PROOF_REVIEW_NOT_READ',
            'correctness-gate disclaimer mismatch')
    expected = {r['path'] for r in j['files']}
    actual = set()
    for root, dirs, files in os.walk(b, followlinks=False):
        for d in dirs:
            p = pathlib.Path(root) / d
            require(not p.is_symlink(), 'unsafe directory link: ' + str(p))
        for f in files:
            p = pathlib.Path(root) / f
            rel = p.relative_to(b).as_posix()
            require(not p.is_symlink(), 'unsafe payload link: ' + rel)
            require(p.is_file() and not p.is_symlink(),
                    'nonregular payload file: ' + rel)
            if rel != 'MANIFEST.json':
                actual.add(rel)
    require(expected == actual, 'public membership mismatch')
    for r in j['files']:
        p = b / r['path']
        require(not p.is_symlink() and p.stat().st_nlink == 1,
                'unsafe payload link: ' + r['path'])
        require(digest(p) == r['sha256'], 'payload hash mismatch: ' + r['path'])
    print(json.dumps({'status': 'PASS_IDENTITY_ONLY',
                      'review_files': len(expected),
                      'mathematics_verified': False}))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError) as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
