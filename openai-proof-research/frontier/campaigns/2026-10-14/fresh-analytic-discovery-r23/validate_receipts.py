#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Exact packet membership and byte provenance checks; not a proof checker."""
from pathlib import Path, PurePosixPath
import hashlib
import json

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[3]


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def check_membership(expected, actual):
    missing, extra = expected - actual, actual - expected
    if missing or extra:
        raise ValueError(f"Packet membership mismatch: missing={sorted(missing)}, extra={sorted(extra)}")


def main():
    manifest = json.loads((BASE / 'manifest.json').read_text())
    rows = manifest['files']
    names = [r['path'] for r in rows]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate manifest paths')
    for name in names:
        path = PurePosixPath(name)
        if path.is_absolute() or '..' in path.parts or name != path.as_posix():
            raise ValueError(f'Unsafe/noncanonical manifest path: {name}')
    expected = set(names)
    actual = set()
    for path in BASE.rglob('*'):
        if path.is_symlink():
            raise ValueError(f'Symlink not permitted: {path}')
        if path.is_file() and path != BASE / 'manifest.json':
            actual.add(path.relative_to(BASE).as_posix())
    check_membership(expected, actual)
    for row in rows:
        data = (BASE / row['path']).read_bytes()
        if len(data) != row['bytes'] or sha256(data) != row['sha256']:
            raise ValueError(f'Byte mismatch: {row["path"]}')

    tree = json.loads((REPO / 'sources/preprints-tree.json').read_text())
    blobs = {r['path']: r['sha'] for r in tree['tree'] if r['type'] == 'blob'}
    source_rows = json.loads((BASE / 'inputs/private/source-receipt.json').read_text())
    for row in source_rows:
        local = REPO / row['local']
        if not local.resolve().is_relative_to(BASE):
            raise ValueError(f'Source outside packet: {local}')
        data = local.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != row['gitblob'] or blob != blobs[row['path']] or sha256(data) != row['sha256']:
            raise ValueError(f'Source identity mismatch: {row["path"]}')
    for stem, receipt in [('florit-simon', 'primary-receipt'), ('liu-et-al-sheeting', 'sheeting-receipt')]:
        row = json.loads((BASE / f'inputs/private/{receipt}.json').read_text())
        if sha256((BASE / f'inputs/private/{stem}.pdf').read_bytes()) != row['sha256']:
            raise ValueError(f'Primary PDF mismatch: {stem}')

    # Exercise both rejection branches without adding/removing any packet file.
    for simulated in [actual | {'__unexpected_payload__'}, actual - {next(iter(actual))}]:
        try:
            check_membership(expected, simulated)
        except ValueError:
            pass
        else:
            raise AssertionError('Membership rejection self-check failed')
    print(f'Verified exact membership and hashes of {len(rows)} payloads, '
          f'{len(source_rows)} pinned Git blobs, and 2 primary PDFs. '
          'Extra/missing membership rejection self-checks passed. '
          'This is not a proof or contribution check.')


if __name__ == '__main__':
    main()
