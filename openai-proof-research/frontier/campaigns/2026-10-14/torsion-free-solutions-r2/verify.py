#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Offline, read-only exact integrity verifier; no mathematical certification."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[3]
CONTROLS = {'inputs-manifest.json', 'outputs-manifest.json', 'seal.json'}
R13 = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r13'
R13_ANCHOR = '8f63c20d76e63f0072b687c2c902462cb121b67b111b4e19b5ca6b7b47b7e23d'
SCOPE = 'be98807412ea2c5fc4a2b71f44ce63ee3f46bc21d4c6522185a56a92b46f9c06'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def guard(event, args):
    if event == 'open':
        mode = args[1] if len(args) > 1 else None
        flags = args[2] if len(args) > 2 else 0
        if isinstance(mode, str) and any(c in mode for c in 'wax+'):
            raise PermissionError('read-only verifier: open')
        if isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT |
                                              os.O_TRUNC | os.O_APPEND):
            raise PermissionError('read-only verifier: flags')
    if event.startswith(('socket.', 'subprocess.', 'ctypes.')) or event in {
        'os.system', 'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.link',
        'os.symlink', 'os.truncate', 'os.chmod', 'os.chown', 'os.utime',
        'os.exec', 'os.posix_spawn', 'os.fork', 'os.chdir',
    }:
        raise PermissionError('read-only verifier: ' + event)


sys.addaudithook(guard)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(base, name):
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or any(v in {'.', '..'} for v in p.parts):
        raise ValueError('unsafe manifest path')
    result = base.joinpath(*p.parts)
    if result.is_symlink() or base.resolve() not in result.resolve().parents:
        raise ValueError('symlink or escaped path')
    return result


def record(base, name):
    b = safe(base, name).read_bytes()
    return {'path': name, 'size': len(b), 'sha256': sha(b)}


def check(base, entry):
    if record(base, entry['path']) != {k: entry[k] for k in ('path', 'size', 'sha256')}:
        raise ValueError('record mismatch: ' + entry['path'])


def load(name):
    return json.loads(safe(ROOT, name).read_bytes())


def snapshot(base):
    result = {}
    for p in sorted(base.rglob('*')):
        if p.is_symlink():
            raise ValueError('symlink in protected tree')
        if p.is_file():
            name = p.relative_to(base).as_posix()
            result[name] = record(base, name)
    return result


def canonical_hash(value):
    return sha(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def main():
    before = snapshot(ROOT)
    ext = load('external-references.json')['files']
    external_before = [record(PROJECT, e['path']) for e in ext]
    result = {}
    code = 1
    try:
        anchor = sha((ROOT / 'seal.json').read_bytes())
        if len(sys.argv) != 2 or sys.argv[1] != anchor:
            raise ValueError('external seal anchor mismatch')
        seal = load('seal.json')
        if seal['schema'] != 'tfs-r2-exact-membership-v1' or set(seal['controls']) != CONTROLS:
            raise ValueError('seal schema/controls mismatch')
        if {e['path'] for e in seal['manifests']} != CONTROLS - {'seal.json'}:
            raise ValueError('manifest membership')
        for e in seal['manifests']:
            check(ROOT, e)
        ins = load('inputs-manifest.json')['files']
        outs = load('outputs-manifest.json')['files']
        names = [e['path'] for e in ins + outs]
        if len(names) != len(set(names)) or set(names) & CONTROLS:
            raise ValueError('duplicate/control payload')
        if any(not e['path'].startswith('inputs/') for e in ins):
            raise ValueError('input classification')
        if any(e['path'].startswith('inputs/') for e in outs):
            raise ValueError('output classification')
        if set(before) != set(names) | CONTROLS:
            raise ValueError('exact owned membership mismatch')
        for e in ins + outs:
            check(ROOT, e)
        if len(ext) != 41 or len({e['path'] for e in ext}) != 41:
            raise ValueError('external membership count')
        for e in ext:
            check(PROJECT, e)
        r13root = safe(PROJECT, R13)
        r13_before = snapshot(r13root)
        if len(r13_before) != 39 or sha((r13root / 'seal.json').read_bytes()) != R13_ANCHOR:
            raise ValueError('r13 anchor/count')
        oldseal = json.loads((r13root / 'seal.json').read_bytes())
        for e in oldseal['manifests']:
            check(r13root, e)
        oldins = json.loads((r13root / 'inputs-manifest.json').read_bytes())['files']
        oldouts = json.loads((r13root / 'outputs-manifest.json').read_bytes())['files']
        oldnames = [e['path'] for e in oldins + oldouts]
        if len(oldnames) != len(set(oldnames)) or set(r13_before) != set(oldnames) | CONTROLS:
            raise ValueError('r13 exact membership')
        for e in oldins + oldouts:
            check(r13root, e)
        expected_external = {R13 + '/' + n for n in r13_before}
        oldext = json.loads((r13root / 'external-references.json').read_bytes())['files']
        if len(oldext) != 2:
            raise ValueError('r13 historical count')
        expected_external.update(e['path'] for e in oldext)
        if {e['path'] for e in ext} != expected_external:
            raise ValueError('external exact membership mismatch')
        if sha((ROOT / 'original-scope.md').read_bytes()) != SCOPE:
            raise ValueError('scope hash mismatch')
        if (ROOT / 'original-scope.md').read_bytes() != (r13root / 'original-scope.md').read_bytes():
            raise ValueError('scope not byte-identical')
        sources = load('source-records.json')
        tree = json.loads(safe(PROJECT, sources['pinned_git_catalogue']).read_bytes())
        if tree.get('truncated') is not False or len(tree['tree']) != 13223:
            raise ValueError('catalogue completeness')
        entries = {e['path']: e for e in tree['tree']}
        pin_count = 0
        for s in sources['pinned_sources']:
            b = safe(PROJECT, s['project_path']).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            cat = entries[s['upstream_path']]
            if (s['commit'] != PIN or blob != s['git_blob_sha1'] or blob != cat['sha'] or
                    len(b) != cat['size'] or len(b) != s['size'] or sha(b) != s['sha256'] or
                    not b.startswith(b'%PDF')):
                raise ValueError('pinned Git blob mismatch')
            pin_count += 1
        if sources['pin'] != PIN or pin_count != 2:
            raise ValueError('pin/count mismatch')
        for s in sources['retained_private_inputs']:
            check(ROOT, {'path': s['local_path'], 'size': s['size'], 'sha256': s['sha256']})
        receipt = load('unchanged-source-receipt.json')
        if (receipt['external_records_sha256'] != canonical_hash(ext) or
                receipt['input_records_sha256'] != canonical_hash(ins) or
                receipt['external_files'] != len(ext) or receipt['owned_input_files'] != len(ins)):
            raise ValueError('unchanged-source receipt mismatch')
        pre = load('verifier-preexecution.json')
        if pre['verify_py_sha256'] != sha((ROOT / 'verify.py').read_bytes()):
            raise ValueError('preexecution verifier hash')
        status = load('status.json')
        if (status['status'] != 'UNRESOLVED_FULL_TFS_AFTER_TWO_ATTEMPTS' or
                status['counted'] or status['accepted_count'] != 4 or
                status['proof_found'] or status['counterexample_found'] or
                status['independent_mathematical_pass'] or status['substantial_contribution_pass']):
            raise ValueError('unresolved disposition mismatch')
        result = {
            'status': 'ACCEPT_INTEGRITY_ONLY', 'target': status['status'],
            'owned_files': len(before), 'inputs': len(ins), 'outputs': len(outs),
            'controls': len(CONTROLS), 'input_bytes': sum(e['size'] for e in ins),
            'output_bytes': sum(e['size'] for e in outs),
            'external_frozen_files': len(ext), 'r13_owned_files': len(r13_before),
            'pinned_git_blobs': pin_count, 'scope_sha256': SCOPE,
            'counted': False, 'accepted_count': 4, 'seal_sha256': anchor,
            'inputs_manifest_sha256': sha((ROOT / 'inputs-manifest.json').read_bytes()),
            'outputs_manifest_sha256': sha((ROOT / 'outputs-manifest.json').read_bytes()),
        }
        code = 0
    except Exception as exc:
        result = {'status': 'REJECT', 'error': str(exc)}
    finally:
        own_same = before == snapshot(ROOT)
        ext_same = external_before == [record(PROJECT, e['path']) for e in ext]
        result['owned_unchanged'] = own_same
        result['external_unchanged'] = ext_same
        if not own_same or not ext_same:
            result.update(status='REJECT', error='protected bytes changed')
            code = 1
    print(json.dumps(result, sort_keys=True))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
