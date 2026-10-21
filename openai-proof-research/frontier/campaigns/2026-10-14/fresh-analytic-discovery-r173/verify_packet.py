#!/usr/bin/env python3
"""Read-only artifact verification; three detached SHA256 anchors are required.

Run with python -B. This script writes no files and makes no mathematical claim.
It checks this round's exact packet, never an inherited or reduced manifest.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit('ARTIFACT FAILURE: ' + message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for label in ('final', 'manifest', 'report'):
        parser.add_argument('--' + label + '-sha256', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    detached = {'FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
    for name, expected in [('FINAL.md', args.final_sha256),
                           ('MANIFEST.json', args.manifest_sha256),
                           ('REPORT.md', args.report_sha256)]:
        require(len(expected) == 64 and all(c in '0123456789abcdef' for c in expected),
                'invalid explicit anchor for ' + name)
        require(digest((root / name).read_bytes()) == expected, 'detached ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    require(manifest['round'] == 'analytic-r173', 'wrong packet identity')
    seen = set()
    for record in manifest['files']:
        name = record['path']
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and name not in detached,
                'invalid manifest member')
        require(name not in seen, 'duplicate manifest member')
        seen.add(name)
        file = root / name
        require(file.is_file() and not file.is_symlink(), 'missing/nonregular ' + name)
        data = file.read_bytes()
        require(len(data) == record['bytes'] and digest(data) == record['sha256'],
                'payload ' + name)
    actual = set()
    for file in root.rglob('*'):
        require(not file.is_symlink(), 'symlink in packet')
        if file.is_file():
            rel = file.relative_to(root).as_posix()
            if rel not in detached:
                actual.add(rel)
    require(actual == seen, 'exact packet membership')
    controls = json.loads((root / 'private/controls/control.json').read_text())
    positive = (root / 'private/controls/positive.bin').read_bytes()
    changed = (root / 'private/controls/changed.bin').read_bytes()
    require(digest(positive) == controls['expected_sha256'], 'positive copied control')
    require(digest(changed) != controls['expected_sha256'], 'negative copied control')
    print('ARTIFACT MATCH: three explicit detached anchors, ' + str(len(seen)) +
          ' exact payload files, positive/changed copied controls. No mathematical gate.')


if __name__ == '__main__':
    main()
