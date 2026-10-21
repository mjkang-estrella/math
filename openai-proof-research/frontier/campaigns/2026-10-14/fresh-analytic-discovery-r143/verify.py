#!/usr/bin/env python3
"""Read-only r143 integrity check; no mathematical or contribution verdict."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    result = {}
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            path = Path(base) / name
            if path.is_symlink():
                raise ValueError('symlink is outside this packet format: ' + str(path))
        for name in files:
            path = Path(base) / name
            if not path.is_file():
                raise ValueError('nonregular entry')
            relative = path.relative_to(root).as_posix()
            result[relative] = path
    return result

def verify(root, anchors):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a nonsymlink directory')
    for name in sorted(ENVELOPES):
        expected = anchors[name]
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('explicit lowercase SHA256 required for ' + name)
        p = root / name
        if p.is_symlink() or not p.is_file() or digest(p.read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    if manifest.get('format') != 'r143-exact-payload-v1':
        raise ValueError('unknown manifest format')
    if manifest.get('outside_envelopes') != sorted(ENVELOPES):
        raise ValueError('envelope exclusion mismatch')
    expected = {}
    for row in manifest['files']:
        name = row['path']
        path = PurePosixPath(name)
        if (not isinstance(name, str) or not name or path.is_absolute()
                or '..' in path.parts or name != path.as_posix()
                or name == '.' or '\\' in name or name in ENVELOPES or name in expected):
            raise ValueError('invalid/duplicate payload path')
        expected[name] = row
    actual = inventory(root)
    payload = set(actual) - ENVELOPES
    if payload != set(expected):
        raise ValueError('exact payload membership mismatch: missing=' + str(sorted(set(expected)-payload))
                         + ' extra=' + str(sorted(payload-set(expected))))
    for name in sorted(payload):
        data = actual[name].read_bytes()
        row = expected[name]
        if len(data) != row['size'] or digest(data) != row['sha256']:
            raise ValueError('payload content mismatch: ' + name)
    return {'integrity': 'match', 'payload_files': len(payload), 'outside_envelopes': 3,
            'mathematical_gate': False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root, {'FINAL.md': args.final_sha256,
                                   'MANIFEST.json': args.manifest_sha256,
                                   'REPORT.md': args.report_sha256})
        print(json.dumps(result, sort_keys=True))
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print(json.dumps({'integrity': 'FAIL', 'reason': str(exc)}))
        raise SystemExit(1)

if __name__ == '__main__':
    main()
