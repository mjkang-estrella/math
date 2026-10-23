#!/usr/bin/env python3
"""Read-only packet verification. Supply all detached anchors explicitly."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(root, final_sha, manifest_sha, report_sha):
    for rel, expected in [('packet/FINAL.md', final_sha),
                          ('MANIFEST.json', manifest_sha),
                          ('REPORT.md', report_sha)]:
        p = root / rel
        if p.is_symlink() or not p.is_file() or digest(p) != expected:
            raise ValueError('detached anchor mismatch: ' + rel)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('format') != 'Arithmetic162f-packet-v1':
        raise ValueError('unexpected manifest format')
    expected = manifest['files']
    actual = {}
    for p in (root / 'packet').rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in packet: ' + str(p))
        if p.is_file():
            rel = p.relative_to(root).as_posix()
            actual[rel] = {'size': p.stat().st_size, 'sha256': digest(p)}
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(k for k in set(actual) & set(expected)
                         if actual[k] != expected[k])
        raise ValueError(json.dumps({'missing': missing, 'extra': extra,
                                     'changed': changed}, sort_keys=True))
    return {'matched_files': len(actual),
            'matched_bytes': sum(x['size'] for x in actual.values()),
            'detached_anchors': 3, 'writes': 0,
            'scope': 'artifact bytes and membership only'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root, args.final_sha256,
                        args.manifest_sha256, args.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({'verified': False, 'error': str(exc)}))
        return 1
    print(json.dumps({'verified': True, **result}, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
