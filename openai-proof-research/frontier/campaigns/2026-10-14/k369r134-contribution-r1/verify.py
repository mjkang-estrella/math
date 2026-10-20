#!/usr/bin/env python3
"""Read-only review-artifact verification, using three detached handoff anchors.

No mathematical, correctness, acceptance, formal or release gate is checked.
Regular-file identities only: no empty-directory, mode or hardlink certificate.
"""
import argparse
import fnmatch
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def excluded(name):
    name = name.lower()
    return (name.startswith('t205q140-')
            or name.startswith('k369r134-proof-')
            or fnmatch.fnmatchcase(name, '*arithmetic*r104*')
            or fnmatch.fnmatchcase(name, '*structural*r141*'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    for n in ('final', 'manifest', 'report'):
        ap.add_argument('--' + n + '-sha256', required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    anchors = {'FINAL.json': args.final_sha256,
               'MANIFEST.json': args.manifest_sha256,
               'REPORT.md': args.report_sha256}
    for name, expected in anchors.items():
        p = root / name
        require(len(expected) == 64 and all(c in '0123456789abcdef' for c in expected), 'invalid detached anchor')
        require(p.is_file() and not p.is_symlink(), 'invalid anchor file ' + name)
        require(sha(p) == expected, 'detached hash mismatch ' + name)
    final = json.loads((root / 'FINAL.json').read_text())
    require(final['manifest_sha256'] == args.manifest_sha256, 'FINAL manifest binding')
    require(final['outside_report_sha256'] == args.report_sha256, 'FINAL report binding')
    verifier = root / 'verify.py'
    require(verifier.is_file() and not verifier.is_symlink()
            and sha(verifier) == final['verifier_sha256'], 'verifier identity mismatch')
    records = json.loads((root / 'MANIFEST.json').read_text())['files']
    names = [x['path'] for x in records]
    require(names == sorted(set(names)), 'manifest order or duplicate')
    for n in names:
        p = PurePosixPath(n)
        require(not p.is_absolute() and '..' not in p.parts and p.parts[0] == 'packet', 'unsafe manifest path')
        require(not any(excluded(x) for x in p.parts), 'excluded component in manifest')
    packet = root / 'packet'
    require(packet.is_dir() and not packet.is_symlink(), 'invalid packet root')
    actual = []
    for base, dirs, files in os.walk(packet, followlinks=False):
        for n in dirs:
            require(not excluded(n), 'excluded directory in own packet')
            require(stat.S_ISDIR((Path(base) / n).lstat().st_mode), 'non-directory or symlink in packet')
        for n in files:
            require(not excluded(n), 'excluded filename in own packet')
            p = Path(base) / n
            require(stat.S_ISREG(p.lstat().st_mode), 'nonregular payload')
            actual.append(p.relative_to(root).as_posix())
    require(sorted(actual) == names, 'exact packet file set mismatch')
    for row in records:
        p = root / row['path']
        require(p.stat().st_size == row['bytes'], 'payload size mismatch ' + row['path'])
        require(sha(p) == row['sha256'], 'payload hash mismatch ' + row['path'])
    require(sha(root / final['review']) == final['review_sha256'], 'review binding')
    require(sha(root / final['frozen_scope_copy']) == final['frozen_scope_sha256'], 'scope binding')
    require(final['verdict'] == 'TECHNICAL' and final['conditional_on_correctness'] is True, 'review metadata mismatch')
    print(json.dumps({'artifact_check': 'PASS', 'files': len(records), 'mathematical_gate': False}))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print(json.dumps({'artifact_check': 'FAIL', 'reason': str(e)}), file=sys.stderr)
        sys.exit(1)
