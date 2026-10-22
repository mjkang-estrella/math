#!/usr/bin/env python3
"""Read-only exact-packet verification from three independently supplied anchors.

Usage: python verify_packet.py ROOT --final-sha256 HEX --manifest-sha256 HEX
                              --report-sha256 HEX
No files are written. Artifact integrity is not a mathematical verdict.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys

EXCLUDED = {'private/MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(test, message):
    if not test:
        raise ValueError(message)

def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root).resolve(strict=True)
    require(root.is_dir(), 'root is not a directory')
    for rel, expected in [('FINAL.md', final_sha),
                          ('private/MANIFEST.json', manifest_sha),
                          ('REPORT.md', report_sha)]:
        require(re.fullmatch('[0-9a-f]{64}', expected) is not None,
                'anchor must be lowercase SHA256: ' + rel)
        path = root / rel
        require(not path.is_symlink() and path.is_file(), 'missing/linked anchor: ' + rel)
        require(digest(path.read_bytes()) == expected, 'anchor mismatch: ' + rel)
    obj = json.loads((root / 'private/MANIFEST.json').read_bytes())
    require(obj.get('schema') == 'r193-exact-packet-v1', 'unsupported manifest schema')
    require(set(obj.get('excluded', [])) == EXCLUDED, 'unexpected exclusions')
    expected = {}
    for row in obj['files']:
        rel = row['path']
        path = PurePosixPath(rel)
        require(isinstance(rel, str) and rel == path.as_posix() and
                not path.is_absolute() and '..' not in path.parts and rel not in EXCLUDED,
                'invalid payload path: ' + str(rel))
        require(rel not in expected, 'duplicate path: ' + rel)
        require(isinstance(row['bytes'], int) and row['bytes'] >= 0 and
                re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None,
                'invalid file metadata: ' + rel)
        expected[rel] = row
    require('FINAL.md' in expected, 'FINAL missing from payload')
    actual = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            require(not (Path(directory) / name).is_symlink(), 'symlink in packet')
        for name in files:
            path = Path(directory) / name
            rel = path.relative_to(root).as_posix()
            require(path.is_file(), 'nonregular file: ' + rel)
            if rel not in EXCLUDED:
                actual.add(rel)
    require(actual == set(expected), 'exact inventory mismatch: missing=' +
            str(sorted(set(expected) - actual)) + '; extra=' + str(sorted(actual - set(expected))))
    total = 0
    for rel, row in expected.items():
        b = (root / rel).read_bytes()
        require(len(b) == row['bytes'], 'size mismatch: ' + rel)
        require(digest(b) == row['sha256'], 'payload digest mismatch: ' + rel)
        total += len(b)
    # ANCHORS is a convenience carrier, never the authority for these arguments.
    carrier = root / 'ANCHORS.json'
    if carrier.exists():
        c = json.loads(carrier.read_bytes())
        require(c == {'FINAL.md': final_sha, 'private/MANIFEST.json': manifest_sha,
                      'REPORT.md': report_sha}, 'detached carrier disagrees with explicit anchors')
    return {'artifact_integrity': 'verified', 'payload_files': len(expected),
            'payload_bytes': total, 'mathematical_verdict': None}

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root')
    for name in ['final', 'manifest', 'report']:
        ap.add_argument('--' + name + '-sha256', required=True)
    args = ap.parse_args()
    try:
        out = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('ARTIFACT REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps(out, sort_keys=True))
