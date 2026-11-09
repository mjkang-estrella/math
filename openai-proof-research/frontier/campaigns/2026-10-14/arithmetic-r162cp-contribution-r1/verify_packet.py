#!/usr/bin/env python3
"""Read-only exact packet verification. Supply all three detached SHA256 anchors.

Run with python -B to avoid import bytecode writes when using this as a module.
This verifies artifacts only, not mathematics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

META = {'MANIFEST.json', 'REPORT.md'}
SCHEMA = 'r162cp-contribution-exact-packet-v1'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe(name):
    if not isinstance(name, str) or not name or '\\' in name:
        raise ValueError('unsafe path')
    p = PurePosixPath(name)
    if p.is_absolute() or any(x in ('.', '..') for x in name.split('/')) or p.as_posix() != name:
        raise ValueError('unsafe path: ' + name)
    return name


def inventory(root):
    root = Path(root)
    ds, fs = {}, {}
    def visit(path, rel):
        st = path.lstat()
        if not stat.S_ISDIR(st.st_mode):
            raise ValueError('non-directory or symlink: ' + rel)
        ds[rel] = st.st_mode
        for name in sorted(os.listdir(path)):
            child = path / name
            key = name if rel == '.' else rel + '/' + name
            safe(key)
            cst = child.lstat()
            if stat.S_ISLNK(cst.st_mode):
                raise ValueError('symlink: ' + key)
            if stat.S_ISDIR(cst.st_mode):
                visit(child, key)
            elif stat.S_ISREG(cst.st_mode):
                fs[key] = {'path': key, 'bytes': cst.st_size,
                           'sha256': digest(child.read_bytes()), 'mode': cst.st_mode}
            else:
                raise ValueError('special file: ' + key)
    visit(root, '.')
    return ds, fs


def selection(root):
    """Build candidate data only; never write a manifest."""
    ds, fs = inventory(root)
    return {'schema': SCHEMA,
            'directories': [{'path': p, 'mode': ds[p]} for p in sorted(ds)],
            'files': [fs[p] for p in sorted(fs) if p not in META],
            'metadata_modes': {'MANIFEST.json': stat.S_IFREG | 0o644,
                               'REPORT.md': fs['REPORT.md']['mode']}}


def validate(root, manifest, require_manifest=True):
    """The same membership/hash/mode logic for preflight, controls and sealed verification."""
    if manifest.get('schema') != SCHEMA:
        raise ValueError('schema mismatch')
    rows = manifest['files']
    names = [safe(r['path']) for r in rows]
    if names != sorted(set(names)) or set(names) & META or 'FINAL.md' not in names:
        raise ValueError('unsafe, unsorted, duplicate or incomplete payload selection')
    dirs = manifest['directories']
    dnames = [r['path'] if r['path'] == '.' else safe(r['path']) for r in dirs]
    if dnames != sorted(set(dnames)) or '.' not in dnames:
        raise ValueError('invalid directory selection')
    if set(manifest['metadata_modes']) != META:
        raise ValueError('invalid metadata modes')
    ds, fs = inventory(root)
    expected = set(names) | {'REPORT.md'} | ({'MANIFEST.json'} if require_manifest else set())
    if set(fs) != expected:
        raise ValueError('exact file membership mismatch')
    if [{'path': p, 'mode': ds[p]} for p in sorted(ds)] != dirs:
        raise ValueError('directory membership/full-mode mismatch')
    for row in rows:
        if fs[row['path']] != row:
            raise ValueError('payload length/hash/full-mode mismatch: ' + row['path'])
    for name in META & expected:
        if fs[name]['mode'] != manifest['metadata_modes'][name]:
            raise ValueError('metadata full-mode mismatch: ' + name)
    return len(rows)


def verify(root, final_sha, manifest_sha, report_sha):
    anchors = {'FINAL.md': final_sha, 'MANIFEST.json': manifest_sha, 'REPORT.md': report_sha}
    for name, value in anchors.items():
        if not isinstance(value, str) or not re.fullmatch('[0-9a-f]{64}', value):
            raise ValueError('explicit lowercase SHA256 required: ' + name)
    _, fs = inventory(root)
    for name, value in anchors.items():
        if name not in fs or fs[name]['sha256'] != value:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((Path(root) / 'MANIFEST.json').read_text())
    count = validate(root, manifest)
    return {'ok': True, 'payload_files': count, 'anchors': anchors,
            'meaning': 'artifact integrity only; no mathematical grade'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).absolute().parent)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    a = ap.parse_args()
    try:
        print(json.dumps(verify(a.root, a.final_sha256, a.manifest_sha256, a.report_sha256), indent=2))
    except (ValueError, KeyError, OSError, TypeError) as e:
        ap.exit(1, 'FAIL: ' + str(e) + '\n')


if __name__ == '__main__':
    main()
