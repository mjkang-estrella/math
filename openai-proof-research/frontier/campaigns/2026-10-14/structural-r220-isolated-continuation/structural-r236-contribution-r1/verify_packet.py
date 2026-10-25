#!/usr/bin/env python3
"""Read-only exact-selection, byte, mode and explicit-anchor verifier.
Does not bind directories, reject unselected extras, or evaluate mathematics.
"""
import argparse
import hashlib
import json
import stat
from pathlib import Path, PurePosixPath


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(root, name):
    p = PurePosixPath(name)
    if not isinstance(name, str) or p.is_absolute() or str(p) != name:
        raise ValueError('noncanonical relative path')
    if not p.parts or any(x in ('', '.', '..') for x in p.parts):
        raise ValueError('unsafe relative path')
    current = root
    for component in p.parts:
        current = current / component
        if current.is_symlink():
            raise ValueError('symlink in selected identity')
    info = current.stat()
    if not stat.S_ISREG(info.st_mode):
        raise ValueError('selected identity is not a regular file')
    return current.read_bytes(), f'{stat.S_IMODE(info.st_mode):04o}'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--selection', required=True)
    ap.add_argument('--selection-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    root = Path(args.root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('invalid root')
    raw, _ = read(root, 'MANIFEST.json')
    if sha(raw) != args.manifest_sha256:
        raise ValueError('manifest anchor mismatch')
    manifest = json.loads(raw)
    raw, _ = read(root, args.selection)
    if sha(raw) != args.selection_sha256:
        raise ValueError('selection anchor mismatch')
    selection = json.loads(raw)
    names = selection['files']
    if names != sorted(set(names)):
        raise ValueError('selection must be sorted and unique')
    entries = manifest['files']
    if [x['path'] for x in entries] != names:
        raise ValueError('manifest and explicit selection differ')
    if 'FINAL.md' not in names or args.selection not in names:
        raise ValueError('missing final or selection identity')
    if any(n in names for n in ('MANIFEST.json', 'REPORT.md', 'ANCHORS.json', 'SEAL-VERIFICATION.json')):
        raise ValueError('detached identity included in selection')
    for entry in entries:
        data, mode = read(root, entry['path'])
        if len(data) != entry['bytes'] or sha(data) != entry['sha256']:
            raise ValueError('selected byte identity mismatch: ' + entry['path'])
        if mode != entry['mode']:
            raise ValueError('selected mode mismatch: ' + entry['path'])
    for name, anchor in [('FINAL.md', args.final_sha256), ('REPORT.md', args.report_sha256)]:
        data, _ = read(root, name)
        if sha(data) != anchor:
            raise ValueError('detached anchor mismatch: ' + name)
    print(json.dumps({'verified': True, 'selected_files': len(names),
        'scope': 'explicit selection, bytes, modes, and supplied anchors only',
        'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    main()
