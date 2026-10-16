#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see LICENSE-CODE).
"""Verify a public extraction or the complete local handoff, read-only.

Hashes check consistency. Supply --manifest-sha256 from a trusted external
receipt to authenticate the public manifest before its contents are parsed.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ZIP_NAME = 'kn-minus-edge-manuscript-public.zip'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def safe_path(base, name):
    require(isinstance(name, str), 'non-string path')
    path = PurePosixPath(name)
    require(bool(name) and name == path.as_posix() and not path.is_absolute()
            and '..' not in path.parts and '\\' not in name and ':' not in name,
            f'unsafe path: {name!r}')
    target = base
    for part in path.parts:
        target = target / part
        require(not target.is_symlink(), f'symlink: {name}')
    return target


def read(base, name):
    path = safe_path(base, name)
    require(path.is_file(), f'missing file: {name}')
    return path.read_bytes()


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, f'duplicate JSON key: {key}')
        obj[key] = value
    return obj


def parse(data):
    return json.loads(data, object_pairs_hook=unique_object)


def check_entries(entries, base):
    require(isinstance(entries, list), 'entries must be a list')
    names = []
    for item in entries:
        name = item['path']
        require(name not in names, f'duplicate manifest path: {name}')
        data = read(base, name)
        require(type(item['bytes']) is int and item['bytes'] >= 0,
                f'invalid byte size: {name}')
        require(isinstance(item['sha256'], str) and
                re.fullmatch(r'[0-9a-f]{64}', item['sha256']), f'invalid hash: {name}')
        require(len(data) == item['bytes'] and digest(data) == item['sha256'],
                f'hash/size mismatch: {name}')
        names.append(name)
    return names


def tree_files(base):
    files = set()
    for path in base.rglob('*'):
        require(not path.is_symlink(), f'symlink: {path.relative_to(base)}')
        if path.is_file():
            files.add(path.relative_to(base).as_posix())
        else:
            require(path.is_dir(), f'unsupported entry: {path.relative_to(base)}')
    return files


def verify(args):
    raw_manifest = read(ROOT, 'public-manifest.json')
    if args.manifest_sha256:
        require(digest(raw_manifest) == args.manifest_sha256,
                'external public-manifest hash mismatch')
    manifest = parse(raw_manifest)
    names = check_entries(manifest['files'], ROOT)
    public = parse(read(ROOT, 'public-files.json'))['files']
    require(public == names, 'public manifest differs from allowlist')
    require('public-manifest.json' not in names, 'manifest lists itself')
    require(not any(name.startswith(('work/', 'checks/pages/', 'checks/work-'))
                    for name in names), 'excluded path in allowlist')
    if args.public:
        require(tree_files(ROOT) == set(names) | {'public-manifest.json'},
                'public extraction file membership mismatch')
        return

    zip_data = read(ROOT, ZIP_NAME)  # Report missing ZIP cleanly.
    import io
    with zipfile.ZipFile(io.BytesIO(zip_data)) as archive:
        require(archive.namelist() == names + ['public-manifest.json'],
                'ZIP contents differ from allowlist')
        for item in manifest['files']:
            data = archive.read(item['path'])
            require(len(data) == item['bytes'] and digest(data) == item['sha256'],
                    f'ZIP member mismatch: {item["path"]}')
        require(archive.read('public-manifest.json') == raw_manifest, 'ZIP manifest differs')
    output = parse(read(ROOT, 'output-manifest.json'))
    outputs = check_entries(output['files'], ROOT)
    require('output-manifest.json' not in outputs and 'SHA256SUMS' not in outputs,
            'output manifest lists itself or checksums')
    require(tree_files(ROOT) == set(outputs) | {'output-manifest.json', 'SHA256SUMS'},
            'handoff file membership mismatch')
    checksums = {}
    for line in read(ROOT, 'SHA256SUMS').decode().splitlines():
        expected, name = line.split('  ', 1)
        require(name not in checksums, f'duplicate checksum path: {name}')
        require(digest(read(ROOT, name)) == expected, f'SHA256SUMS mismatch: {name}')
        checksums[name] = expected
    require(set(checksums) == set(outputs) | {'output-manifest.json'},
            'checksum file membership mismatch')
    if args.with_inputs:
        inputs = parse(read(ROOT, 'input-manifest.json'))
        check_entries(inputs['inputs'], ROOT.parents[3])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--public', action='store_true', help='check a clean public ZIP extraction only')
    parser.add_argument('--with-inputs', action='store_true', help='also check repository inputs (full mode only)')
    parser.add_argument('--manifest-sha256', help='trusted external public-manifest SHA256')
    args = parser.parse_args()
    try:
        require(not (args.public and args.with_inputs), '--with-inputs requires full mode')
        verify(args)
    except (OSError, ValueError, KeyError, TypeError, UnicodeError, zipfile.BadZipFile, RuntimeError) as exc:
        print(f'VERIFY FAILED\n  {exc}')
        return 1
    print('VERIFY PASSED' + (' (public extraction)' if args.public else
                           ' (including inputs)' if args.with_inputs else ''))
    return 0


if __name__ == '__main__':
    sys.exit(main())
