#!/usr/bin/env python3
"""Read-only exact-packet verification. Hashes must come from detached evidence.

This program verifies bytes, modes, and membership; it assigns no mathematical gate.
It never reads source/author paths outside the supplied review root.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular(path):
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError('not a regular file: ' + str(path))


def verify(root, final_sha256, manifest_sha256, report_sha256):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a directory, not a symlink')
    packet = root / 'packet'
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError('invalid packet directory')
    for name, anchor in [('packet/FINAL.md', final_sha256), ('MANIFEST.json', manifest_sha256), ('REPORT.md', report_sha256)]:
        if len(anchor) != 64 or any(c not in '0123456789abcdef' for c in anchor):
            raise ValueError('invalid detached hash: ' + name)
        path = root / name
        regular(path)
        if digest(path) != anchor:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    if manifest.get('schema') != 'r162m-proof-r1-exact-v1':
        raise ValueError('unsupported manifest schema')
    expected = {}
    for entry in manifest['entries']:
        name = entry['path']
        posix = PurePosixPath(name)
        if posix.is_absolute() or '..' in posix.parts or posix.as_posix() != name or not (name == 'packet' or name.startswith('packet/')):
            raise ValueError('invalid packet path')
        if name in expected:
            raise ValueError('duplicate path: ' + name)
        expected[name] = entry
    actual = {}
    for parent, dirs, files in os.walk(packet, followlinks=False):
        for path in [Path(parent)] + [Path(parent) / n for n in files] + [Path(parent) / n for n in dirs]:
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode) or not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise ValueError('nonordinary packet entry: ' + str(path))
            name = path.relative_to(root).as_posix()
            if name in actual:
                continue
            rec = {'path': name, 'type': 'directory' if stat.S_ISDIR(mode) else 'file', 'mode': oct(stat.S_IMODE(mode))}
            if rec['type'] == 'file':
                rec.update(bytes=path.stat().st_size, sha256=digest(path))
            actual[name] = rec
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(k for k in set(actual) & set(expected) if actual[k] != expected[k])
        raise ValueError(json.dumps({'missing': missing, 'extra': extra, 'changed': changed}))
    return {'artifact_check': 'OK', 'files': sum(e['type'] == 'file' for e in actual.values()), 'directories': sum(e['type'] == 'directory' for e in actual.values()), 'mathematical_gate_assigned': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root')
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        result = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (ValueError, KeyError, OSError, TypeError, json.JSONDecodeError) as error:
        print('ARTIFACT CHECK FAILED: ' + str(error), file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
