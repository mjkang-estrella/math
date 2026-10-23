#!/usr/bin/env python3
"""Read-only exact review-packet verification with explicit detached anchors."""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

FORMAT = 'structural-r196-contribution-review-v1'
CARRIERS = {'FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe_name(name, directory=False):
    if directory and name == '.':
        return name
    if not isinstance(name, str):
        raise ValueError('non-string path')
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or '..' in p.parts or str(p) != name:
        raise ValueError('unsafe path: ' + name)
    return name

def verify(root, final_sha256, manifest_sha256, report_sha256):
    root = Path(root)
    if root.is_symlink():
        raise ValueError('symlink root')
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError('not a directory')
    anchors = {'FINAL.md': final_sha256, 'MANIFEST.json': manifest_sha256,
               'REPORT.md': report_sha256}
    for name, expected in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('invalid explicit anchor: ' + name)
        path = root / name
        if path.is_symlink() or not path.is_file() or digest(path.read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_bytes())
    if manifest.get('format') != FORMAT:
        raise ValueError('unexpected manifest format')
    selected = {}
    for item in manifest['files']:
        name = safe_name(item['path'])
        if name in selected or name in CARRIERS:
            raise ValueError('duplicate/detached selected path: ' + name)
        selected[name] = item
    detached = {safe_name(i['path']): i for i in manifest['detached']}
    if set(detached) != CARRIERS or len(manifest['detached']) != len(CARRIERS):
        raise ValueError('detached selection mismatch')
    directories = {safe_name(i['path'], True): i for i in manifest['directories']}
    if '.' not in directories or len(directories) != len(manifest['directories']):
        raise ValueError('directory selection mismatch')
    actual_files, actual_dirs = {}, {'.': stat.S_IMODE(root.stat().st_mode)}
    for parent, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            path = Path(parent) / name
            mode = path.lstat().st_mode
            rel = path.relative_to(root).as_posix()
            if stat.S_ISLNK(mode):
                raise ValueError('symlink: ' + rel)
            if stat.S_ISDIR(mode):
                actual_dirs[rel] = stat.S_IMODE(mode)
            elif stat.S_ISREG(mode):
                actual_files[rel] = stat.S_IMODE(mode)
            else:
                raise ValueError('non-regular entry: ' + rel)
    if set(actual_files) != set(selected) | CARRIERS:
        raise ValueError('exact file selection mismatch')
    if set(actual_dirs) != set(directories):
        raise ValueError('exact directory selection mismatch')
    for name, item in directories.items():
        if actual_dirs[name] != item['mode']:
            raise ValueError('directory mode mismatch: ' + name)
    for name, item in {**selected, **detached}.items():
        if actual_files[name] != item['mode']:
            raise ValueError('file mode mismatch: ' + name)
    for name, item in selected.items():
        b = (root / name).read_bytes()
        if len(b) != item['bytes'] or digest(b) != item['sha256']:
            raise ValueError('selected bytes mismatch: ' + name)
    canonical_carrier = (json.dumps(anchors, indent=2, sort_keys=True) + '\n').encode()
    if (root / 'ANCHORS.json').read_bytes() != canonical_carrier:
        raise ValueError('anchor carrier mismatch')
    return {'integrity': 'PASS', 'selected_files': len(selected),
            'detached_files': len(CARRIERS), 'directories': len(directories),
            'exact_selection_and_modes': True, 'mathematical_grade': None}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    try:
        print(json.dumps(verify(**vars(parser.parse_args())), sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('integrity error: ' + str(exc), file=sys.stderr)
        sys.exit(1)
