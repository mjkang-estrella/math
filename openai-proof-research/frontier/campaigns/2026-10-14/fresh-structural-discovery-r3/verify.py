#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only offline authentication followed by an exact diagnostic replay.

This program has no seal/receipt creation or repair mode. Authenticate the
detached seal.json SHA256 from the handoff before trusting this package.
"""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_rel(name):
    p = ROOT / name
    if p.is_symlink() or not p.resolve().is_relative_to(ROOT):
        raise ValueError('unsafe path: ' + name)
    return p.read_bytes()


def verify():
    # All stored bytes, including the receipt, are authenticated BEFORE any
    # checker is loaded or run. No receipt is regenerated as authentication.
    seal = json.loads(read_rel('seal.json'))
    inventories = []
    for manifest_name in ['inputs-manifest.json', 'outputs-manifest.json']:
        data = read_rel(manifest_name)
        if digest(data) != seal['manifests'][manifest_name]['sha256']:
            raise ValueError('manifest digest mismatch: ' + manifest_name)
        if len(data) != seal['manifests'][manifest_name]['size']:
            raise ValueError('manifest size mismatch: ' + manifest_name)
        inventory = json.loads(data)['files']
        paths = [x['path'] for x in inventory]
        if paths != sorted(set(paths)):
            raise ValueError('inventory is not sorted and unique')
        for entry in inventory:
            data = read_rel(entry['path'])
            if len(data) != entry['size'] or digest(data) != entry['sha256']:
                raise ValueError('file authentication failed: ' + entry['path'])
        inventories.append(inventory)
    expected = {e['path'] for inv in inventories for e in inv}
    expected.update(['seal.json', 'inputs-manifest.json', 'outputs-manifest.json'])
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()}
    if actual != expected:
        raise ValueError('inventory mismatch: ' + repr(sorted(actual ^ expected)))
    if any(p.is_symlink() for p in ROOT.rglob('*')):
        raise ValueError('symlinks are not allowed')
    for row in json.loads(read_rel('retrieval-upstream.json')):
        data = read_rel(row['path'])
        git_blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if git_blob != row['git_blob']:
            raise ValueError('Git blob mismatch: ' + row['path'])

    # Defence in depth: the replay can import standard-library code but may
    # not write files, launch processes, load a network connection, or mutate
    # the filesystem. It receives only the already authenticated checker.
    def read_only_audit(event, args):
        if event == 'open':
            mode, flags = args[1:3]
            if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
                    isinstance(flags, int) and flags & (1 | 2 | 64 | 512 | 1024)):
                raise RuntimeError('read-only verifier blocked file write')
        if event.startswith(('socket.', 'subprocess.')) or event in {
                'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.chmod',
                'os.link', 'os.symlink', 'os.system', 'os.truncate',
                'os.utime', 'os.exec', 'os.posix_spawn'}:
            raise RuntimeError('read-only verifier blocked: ' + event)
    sys.addaudithook(read_only_audit)
    checker_bytes = read_rel('checks.py')
    scope = {'__name__': 'authenticated_supporting_checks', '__file__': str(ROOT/'checks.py')}
    exec(compile(checker_bytes, str(ROOT/'checks.py'), 'exec'), scope)
    replay = (json.dumps(scope['run'](), indent=2, sort_keys=True)+'\n').encode()
    if replay != read_rel('checks.json'):
        raise ValueError('authenticated receipt differs from deterministic replay')
    print(json.dumps({'status': 'PASS', 'input_files': len(inventories[0]),
                      'output_files': len(inventories[1]),
                      'pinned_blobs': len(json.loads(read_rel('retrieval-upstream.json'))),
                      'receipt_sha256': digest(replay),
                      'writes': 0, 'network': False,
                      'scope': 'Integrity and finite checks only; not independent mathematical review.'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    verify()
