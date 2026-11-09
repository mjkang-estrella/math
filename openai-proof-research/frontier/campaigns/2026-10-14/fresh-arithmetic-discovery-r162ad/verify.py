#!/usr/bin/env python3
"""Read-only byte/membership verification. Not a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, supplied):
    root = Path(root)
    if root.is_symlink():
        raise ValueError('symlink root')
    actual = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            if (Path(base) / name).is_symlink():
                raise ValueError('symlink in selection')
        for name in files:
            actual.add((Path(base) / name).relative_to(root).as_posix())
    for name, anchor in supplied.items():
        if len(anchor) != 64 or any(c not in '0123456789abcdef' for c in anchor):
            raise ValueError('invalid explicit anchor')
        if digest((root / name).read_bytes()) != anchor:
            raise ValueError('detached anchor mismatch: ' + name)
    detached = json.loads((root / 'ANCHORS.json').read_text())
    if detached != supplied:
        raise ValueError('ANCHORS differs from explicit anchors')
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    entries = manifest['files']
    expected = set()
    total = 0
    for entry in entries:
        rel = entry['path']
        pp = PurePosixPath(rel)
        if pp.is_absolute() or '..' in pp.parts or pp.as_posix() != rel:
            raise ValueError('unsafe manifest path')
        if rel in expected:
            raise ValueError('duplicate manifest member')
        expected.add(rel)
        raw = (root / rel).read_bytes()
        if len(raw) != entry['bytes'] or digest(raw) != entry['sha256']:
            raise ValueError('member mismatch: ' + rel)
        total += len(raw)
    if not {'FINAL.md', 'verify.py'}.issubset(expected):
        raise ValueError('missing self-contained handoff/verifier')
    if actual != expected | {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}:
        raise ValueError('exact membership mismatch')
    authpath = root / 'packet/private/authentication.json'
    bindings = 0
    if authpath.exists():
        rows = json.loads(authpath.read_text())
        tree = json.loads((root / 'packet/private/canonical-tree-selection.json').read_text())
        blobs = {e['path']: e for e in tree if e['type'] == 'blob'}
        if len(rows) != 11 or len(blobs) != 11 or {x['path'] for x in rows} != set(blobs):
            raise ValueError('canonical selection count/path mismatch')
        for row in rows:
            if row['local'] not in expected:
                raise ValueError('canonical member not manifested')
            raw = (root / row['local']).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            entry = blobs[row['path']]
            if len(raw) != entry['size'] or len(raw) != row['size']:
                raise ValueError('canonical size mismatch')
            if blob != entry['sha'] or blob != row['git_blob'] or digest(raw) != row['sha256']:
                raise ValueError('canonical binding mismatch')
            bindings += 1
    return {'artifact_integrity_only': True, 'files': len(entries), 'bytes': total,
            'canonical_bindings': bindings, 'writes': 0,
            'limitations': 'File bytes and membership only; no directory/mode identity or mathematical gate.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', required=True)
    p.add_argument('--final-sha256', required=True)
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--report-sha256', required=True)
    a = p.parse_args()
    supplied = {'FINAL.md': a.final_sha256, 'MANIFEST.json': a.manifest_sha256,
                'REPORT.md': a.report_sha256}
    try:
        print(json.dumps(verify(a.root, supplied), sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('ARTIFACT VERIFICATION FAILED: ' + str(exc))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
