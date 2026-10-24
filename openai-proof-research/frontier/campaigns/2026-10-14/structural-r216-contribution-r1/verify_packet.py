#!/usr/bin/env python3
"""Read-only exact-packet verification against four explicit detached anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_path(value):
    require(isinstance(value, str), 'non-string path')
    if value == '.':
        return value
    p = PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and str(p) == value,
            'noncanonical relative path')
    return value


def inventory(root):
    require(not root.is_symlink() and root.is_dir(), 'packet is not an ordinary directory')
    out = []
    def walk(path, rel):
        s = path.lstat()
        require(stat.S_ISDIR(s.st_mode), 'non-directory in traversal')
        out.append({'path': rel, 'type': 'directory', 'mode': stat.S_IMODE(s.st_mode)})
        with os.scandir(path) as entries:
            names = sorted(entry.name for entry in entries)
        for name in names:
            child = path / name
            key = name if rel == '.' else rel + '/' + name
            t = child.lstat()
            require(not stat.S_ISLNK(t.st_mode), 'symlink rejected: ' + key)
            if stat.S_ISDIR(t.st_mode):
                walk(child, key)
            else:
                require(stat.S_ISREG(t.st_mode), 'nonregular file rejected: ' + key)
                out.append({'path': key, 'type': 'file', 'mode': stat.S_IMODE(t.st_mode),
                            'size': t.st_size, 'sha256': sha(child)})
    walk(root, '.')
    return sorted(out, key=lambda x: x['path'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('packet', 'manifest', 'selection', 'report',
                 'final-sha', 'manifest-sha', 'selection-sha', 'report-sha'):
        p.add_argument('--' + name, required=True)
    args = p.parse_args()
    packet = Path(args.packet)
    locations = {'final': packet / 'FINAL.md', 'manifest': Path(args.manifest),
                 'selection': Path(args.selection), 'report': Path(args.report)}
    for label, path in locations.items():
        anchor = getattr(args, label + '_sha')
        require(re.fullmatch('[0-9a-f]{64}', anchor) is not None, 'invalid explicit anchor: ' + label)
        require(not path.is_symlink() and path.is_file(), 'anchor target is not ordinary file: ' + label)
        require(sha(path) == anchor, 'anchor mismatch: ' + label)
    selection = json.loads(locations['selection'].read_bytes())
    manifest = json.loads(locations['manifest'].read_bytes())
    require(selection['schema'] == 'structural216-review-selection-v1', 'selection schema')
    require(manifest['schema'] == 'structural216-review-manifest-v1', 'manifest schema')
    require(manifest['selection_sha256'] == args.selection_sha, 'manifest selection binding')
    selected = {safe_path(k): v for k, v in selection['entries'].items()}
    require(selected.get('.') == 'directory' and selected.get('FINAL.md') == 'file', 'required selection entries')
    expected = manifest['entries']
    require(len(expected) == len({safe_path(x['path']) for x in expected}), 'duplicate manifest path')
    require({x['path']: x['type'] for x in expected} == selected, 'selection/manifest mismatch')
    actual = inventory(packet)
    require({x['path']: x['type'] for x in actual} == selected, 'actual exact-selection mismatch')
    require(actual == sorted(expected, key=lambda x: x['path']), 'bytes, sizes or modes mismatch')
    print(json.dumps({'artifact_verification': 'matches four explicit anchors, exact selection, bytes and modes',
                      'files': sum(x['type'] == 'file' for x in actual), 'entries': len(actual),
                      'read_only': True, 'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as exc:
        print(json.dumps({'artifact_verification': 'REJECTED', 'reason': str(exc),
                          'mathematical_gate': False}, sort_keys=True), file=sys.stderr)
        sys.exit(1)
