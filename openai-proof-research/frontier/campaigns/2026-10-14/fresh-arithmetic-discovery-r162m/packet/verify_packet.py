#!/usr/bin/env python3
"""Read-only exact packet verifier. Detached hashes must be supplied explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def inventory(root):
    files, directories = {}, []
    start = root / 'packet'
    if start.is_symlink() or not start.is_dir():
        raise ValueError('packet is absent or a symlink')
    for directory, names, leaves in os.walk(start, followlinks=False):
        here = Path(directory)
        directories.append(here.relative_to(root).as_posix())
        for name in names:
            if (here / name).is_symlink():
                raise ValueError('directory symlink')
        for name in leaves:
            p = here / name
            if p.is_symlink() or not p.is_file():
                raise ValueError('nonregular packet object')
            files[p.relative_to(root).as_posix()] = p
    return files, sorted(directories)


def verify(root, final_sha, manifest_sha, report_sha):
    for name, wanted in [('packet/FINAL.md', final_sha),
                         ('MANIFEST.json', manifest_sha), ('REPORT.md', report_sha)]:
        if len(wanted) != 64 or any(c not in '0123456789abcdef' for c in wanted):
            raise ValueError('invalid explicit detached anchor')
        path = root / name
        if path.is_symlink() or not path.is_file() or digest(path) != wanted:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    if manifest.get('format') != 'r162m-exact-packet-v1' or manifest.get('scope') != 'packet/':
        raise ValueError('manifest format/scope mismatch')
    actual, directories = inventory(root)
    entries = manifest['files']
    expected = {}
    for entry in entries:
        name = entry['path']
        path = PurePosixPath(name)
        if (not isinstance(name, str) or path.is_absolute() or '..' in path.parts
                or not name.startswith('packet/') or path.as_posix() != name
                or name in expected):
            raise ValueError('invalid or duplicate manifest path')
        expected[name] = entry
    if set(actual) != set(expected):
        raise ValueError('exact file set mismatch')
    if directories != manifest['directories']:
        raise ValueError('exact directory set mismatch')
    for name, path in actual.items():
        entry = expected[name]
        if path.stat().st_size != entry['bytes'] or digest(path) != entry['sha256']:
            raise ValueError('packet byte mismatch: ' + name)
    return len(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    try:
        count = verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('ARTIFACT MISMATCH:', exc)
        return 1
    print('ARTIFACT BYTES MATCH:', count, 'files; no mathematical gate assigned')
    return 0


if __name__ == '__main__':
    sys.exit(main())
