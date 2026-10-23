#!/usr/bin/env python3
"""Read-only integrity check. Explicit detached anchors are mandatory; no gates."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
sys.dont_write_bytecode = True


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, anchors):
    root = root.resolve(strict=True)

    def local(name):
        p = PurePosixPath(name)
        if not name or p.is_absolute() or '..' in p.parts or str(p) != name:
            raise ValueError('unsafe manifest path')
        q = root
        for part in p.parts:
            q = q / part
            if q.is_symlink():
                raise ValueError('symlink forbidden: ' + name)
        if not q.is_file():
            raise ValueError('missing file: ' + name)
        return q

    for name, expected in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('anchor must be lowercase SHA256')
        if sha(local(name).read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    m = json.loads(local('private/MANIFEST.json').read_text())
    if m['format'] != 'r162r-exact-packet-v1' or m['scopes'] != ['packet']:
        raise ValueError('unsupported manifest schema')
    if m['additional_files'] not in ([], ['verify_packet.py']):
        raise ValueError('unexpected additional files')
    observed = set(m['additional_files'])
    packet = root / 'packet'
    if not packet.is_dir() or packet.is_symlink():
        raise ValueError('missing or symbolic packet directory')
    for p in packet.rglob('*'):
        if p.is_symlink():
            raise ValueError('symbolic packet member')
        if p.is_file():
            observed.add(p.relative_to(root).as_posix())
    entries = m['entries']
    names = [e['path'] for e in entries]
    if len(set(names)) != len(names) or set(names) != observed:
        raise ValueError('manifest does not match exact payload inventory')
    for e in entries:
        b = local(e['path']).read_bytes()
        if len(b) != e['bytes'] or sha(b) != e['sha256']:
            raise ValueError('payload mismatch: ' + e['path'])
    auth_name = 'packet/private/canonical-authentication.json'
    if auth_name in observed:
        auth = json.loads(local(auth_name).read_text())
        tree = json.loads(local('packet/private/canonical-tree-selection.json').read_text())
        blobs = {e['path']: e for e in tree if e['type'] == 'blob'}
        if len(auth) != 39 or len(blobs) != 39 or {a['path'] for a in auth} != set(blobs):
            raise ValueError('canonical selection mismatch')
        for a in auth:
            b = local(a['local']).read_bytes()
            git = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            t = blobs[a['path']]
            if not (len(b) == a['bytes'] == t['size'] and git == a['git_blob'] == t['sha'] and sha(b) == a['sha256']):
                raise ValueError('canonical authentication mismatch')
    primary_name = 'packet/private/primary-local-objects.json'
    if primary_name in observed:
        for a in json.loads(local(primary_name).read_text()):
            b = local(a['local']).read_bytes()
            if len(b) != a['bytes'] or sha(b) != a['sha256']:
                raise ValueError('primary local object mismatch')
    return len(entries)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--final-sha256', required=True)
    ap.add_argument('--manifest-sha256', required=True)
    ap.add_argument('--report-sha256', required=True)
    args = ap.parse_args()
    try:
        n = verify(args.root, {'FINAL.md': args.final_sha256,
                              'private/MANIFEST.json': args.manifest_sha256,
                              'REPORT.md': args.report_sha256})
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('INTEGRITY FAILURE:', exc, file=sys.stderr)
        return 1
    print('Integrity verified:', n, 'payload files; three explicit detached anchors. No mathematical gate assigned.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
