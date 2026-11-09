#!/usr/bin/env python3
"""Read-only externally anchored review verifier. MIT, copyright 2026 Myeongjin Kang.
Adapted from t088p133-formal-v1/packet/public/verify.py; original unchanged.
Run a trusted copy of this script. It does not establish mathematics or acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import stat


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def record(path):
    s = path.lstat()
    r = {'mode': stat.S_IMODE(s.st_mode), 'nlink': s.st_nlink,
         'kind': 'dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'link'}
    if r['kind'] == 'file':
        r.update(bytes=s.st_size, sha256=sha(path))
    if r['kind'] == 'link':
        r['target'] = str(path.readlink())
    return r


def ordinary(path):
    s = path.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_nlink == 1 and stat.S_IMODE(s.st_mode) == 0o644,
            'nonordinary sealed file: '+str(path))


def verify(root, final_hash, manifest_hash, report_hash, originals=None):
    require(not root.is_symlink(), 'linked package root')
    root = root.resolve()
    for rel, expected in [('FINAL.json', final_hash), ('packet/MANIFEST.json', manifest_hash),
                          ('REPORT.md', report_hash)]:
        ordinary(root/rel)
        require(sha(root/rel) == expected, 'external anchor mismatch: '+rel)
    require((root/'packet').is_dir() and not (root/'packet').is_symlink(), 'linked or missing packet')
    manifest = json.loads((root/'packet/MANIFEST.json').read_text())
    actual = {}
    for p in [root/'packet', *sorted((root/'packet').rglob('*'))]:
        if p == root/'packet/MANIFEST.json':
            continue
        require(not p.is_symlink(), 'linked payload: '+str(p))
        actual[str(p.relative_to(root))] = record(p)
    require(set(actual) == set(manifest['entries']), 'packet path set mismatch')
    for rel, expected in manifest['entries'].items():
        require(actual[rel] == expected, 'payload metadata/hash mismatch: '+rel)
    final = json.loads((root/'FINAL.json').read_text())
    require(final['manifest_sha256'] == manifest_hash and final['outside_report_sha256'] == report_hash,
            'final binding mismatch')
    checked_originals = 0
    if originals is not None:
        inventory = json.loads((root/'packet/public/originals-before.json').read_text())
        before = inventory['entries']
        observations = {'frontier/NEW-TEN-2026-10-14.md',
            'frontier/campaigns/2026-10-14/discovery-analytic-r133-parent/formal-review-r1-dispatch.json'}
        for rel, expected in before.items():
            if rel not in observations:
                require(record(originals/rel) == expected, 'original changed: '+rel)
        for rel in inventory['complete_roots']:
            tree = originals/rel
            paths = {str(p.relative_to(originals)) for p in [tree, *tree.rglob('*')]}
            expected_paths = {p for p in before if p == rel or p.startswith(rel+'/')}
            require(paths == expected_paths, 'original layout changed: '+rel)
        checked_originals = len(before)-len(observations)

    return {'artifact_check': 'OK', 'payload_entries': len(actual), 'original_entries_checked': checked_originals,
            'coverage': 'sealed packet hashes/modes/link counts/layout plus three external anchors; work excluded',
            'mathematical_review': False}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    ap.add_argument('--originals', type=Path)
    a = ap.parse_args()
    print(json.dumps(verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256, a.originals), indent=2))

if __name__ == '__main__':
    main()
