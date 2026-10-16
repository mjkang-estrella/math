#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Offline, read-only integrity checks. No mathematical certification."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[3]
CONTROLS = {'inputs-manifest.json', 'outputs-manifest.json', 'seal.json'}
SCOPE_SHA = 'be98807412ea2c5fc4a2b71f44ce63ee3f46bc21d4c6522185a56a92b46f9c06'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def guard(event, args):
    if event == 'open':
        mode = args[1] if len(args) > 1 else None
        flags = args[2] if len(args) > 2 else 0
        if isinstance(mode, str) and any(c in mode for c in 'wax+'):
            raise PermissionError('read-only verifier: open')
        write_flags = os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND
        if isinstance(flags, int) and flags & write_flags:
            raise PermissionError('read-only verifier: flags')
    if event.startswith(('socket.', 'subprocess.', 'ctypes.')) or event in {
        'os.system', 'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir',
        'os.link', 'os.symlink', 'os.truncate', 'os.chmod', 'os.chown',
        'os.utime', 'os.exec', 'os.posix_spawn', 'os.fork', 'os.chdir',
    }:
        raise PermissionError('read-only verifier: ' + event)


sys.addaudithook(guard)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def resolve(base, name):
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or any(x in {'..', '.'} for x in p.parts):
        raise ValueError('unsafe manifest path')
    result = base.joinpath(*p.parts)
    if result.is_symlink() or base.resolve() not in result.resolve().parents:
        raise ValueError('symlink or escaped path')
    return result


def record(base, name):
    b = resolve(base, name).read_bytes()
    return {'path': name, 'size': len(b), 'sha256': digest(b)}


def snapshot():
    result = {}
    for p in sorted(ROOT.rglob('*')):
        if p.is_symlink():
            raise ValueError('owned symlink')
        if p.is_file():
            name = p.relative_to(ROOT).as_posix()
            result[name] = record(ROOT, name)
    return result


def check(base, entry):
    actual = record(base, entry['path'])
    if actual['size'] != entry['size'] or actual['sha256'] != entry['sha256']:
        raise ValueError('record mismatch: ' + entry['path'])


def load(name):
    return json.loads((ROOT / name).read_bytes())


def main():
    before = snapshot()
    ext = load('external-references.json')['files']
    ext_before = [record(PROJECT, e['path']) for e in ext]
    result = {}
    code = 1
    try:
        if len(sys.argv) != 2 or digest((ROOT / 'seal.json').read_bytes()) != sys.argv[1]:
            raise ValueError('external seal anchor mismatch')
        seal = load('seal.json')
        if seal['schema'] != 'r13-exact-membership-v1':
            raise ValueError('seal schema')
        for e in seal['manifests']:
            check(ROOT, e)
        ins = load('inputs-manifest.json')['files']
        outs = load('outputs-manifest.json')['files']
        names = [e['path'] for e in ins + outs]
        if len(names) != len(set(names)) or set(names) & CONTROLS:
            raise ValueError('duplicate/control payload path')
        if any(not e['path'].startswith('inputs/') for e in ins):
            raise ValueError('input classification')
        if any(e['path'].startswith('inputs/') for e in outs):
            raise ValueError('output classification')
        if set(before) != set(names) | CONTROLS:
            raise ValueError('exact membership mismatch')
        for e in ins + outs:
            check(ROOT, e)
        for e in ext:
            check(PROJECT, e)
        if digest((ROOT / 'original-scope.md').read_bytes()) != SCOPE_SHA:
            raise ValueError('frozen scope mismatch')
        upstream = load('inputs/context/upstream.json')
        if upstream['commit'] != PIN:
            raise ValueError('upstream pin mismatch')
        tree = load('inputs/context/preprints-tree.json')
        if tree.get('truncated') is not False or len(tree['tree']) != 13223:
            raise ValueError('incomplete preprint catalogue')
        entries = {e['path']: e for e in tree['tree']}
        sources = load('source-records.json')['sources']
        pinned = 0
        for s in sources:
            check(ROOT, {'path': s['local_path'], 'size': s['size'], 'sha256': s['sha256']})
            if s['kind'] == 'pinned-upstream':
                b = resolve(ROOT, s['local_path']).read_bytes()
                blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
                cat = entries[s['upstream_path']]
                if (s['commit'] != PIN or blob != s['git_blob_sha1'] or
                        blob != cat['sha'] or len(b) != cat['size'] or not b.startswith(b'%PDF')):
                    raise ValueError('pinned Git blob mismatch')
                pinned += 1
        if pinned != 2:
            raise ValueError('pinned source count mismatch')
        status = load('status.json')
        if status['status'] != 'UNRESOLVED_FULL_TFS' or status['counted'] or status['accepted_count'] != 4:
            raise ValueError('disposition mismatch: no proof/count certification')
        result = {'status': 'ACCEPT_INTEGRITY_ONLY', 'target': 'UNRESOLVED_FULL_TFS',
                  'owned_files': len(before), 'inputs': len(ins), 'outputs': len(outs),
                  'external_frozen_files': len(ext), 'pinned_git_blobs': pinned,
                  'counted': False, 'accepted_count': 4, 'seal_sha256': sys.argv[1]}
        code = 0
    except Exception as exc:
        result = {'status': 'REJECT', 'error': str(exc)}
    finally:
        own_same = before == snapshot()
        ext_same = ext_before == [record(PROJECT, e['path']) for e in ext]
        result['owned_unchanged'] = own_same
        result['external_unchanged'] = ext_same
        if not own_same or not ext_same:
            result['status'] = 'REJECT'
            result['error'] = 'protected bytes changed during verification'
            code = 1
    print(json.dumps(result, sort_keys=True))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
