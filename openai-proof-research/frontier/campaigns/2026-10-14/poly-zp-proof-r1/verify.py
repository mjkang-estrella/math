#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only verifier for the poly-Z_p proof review round 1.

Authenticate the detached SHA256 of seal.json from the handoff first. This
program has no sealing, receipt-writing or repair mode. It authenticates all
inventoried bytes BEFORE compiling the checker, then compares an in-memory
replay with the frozen receipt.
"""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[3]
CANDIDATE = 'frontier/campaigns/2026-10-14/fresh-structural-discovery-r3'
CANDIDATE_MD = 'e3f4c65e5eb0f35e9d19090e0ba897b27219a223795a0569319a3114cb3babcc'
CANDIDATE_SEAL = '75df70d930c3ccd57287e76a082dab1885bb844b0691132201ce2d4a199684e4'
OWN = {'seal.json', 'inputs-manifest.json', 'outputs-manifest.json'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(base, rel):
    p = base / rel
    if p.is_symlink() or not p.resolve().is_relative_to(base):
        raise ValueError('unsafe path: ' + rel)
    return p.read_bytes()


def files_under(base):
    if any(p.is_symlink() for p in base.rglob('*')):
        raise ValueError('symlink under ' + str(base))
    return {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}


def verify():
    seal = json.loads(read(ROOT, 'seal.json'))
    manifests = {}
    for name in ['inputs-manifest.json', 'outputs-manifest.json']:
        data = read(ROOT, name)
        if digest(data) != seal['manifests'][name]['sha256'] or \
                len(data) != seal['manifests'][name]['size']:
            raise ValueError('manifest authentication failed: ' + name)
        manifests[name] = json.loads(data)['files']
    bases = {'project': PROJECT, 'review': ROOT}
    for name, inv in manifests.items():
        keys = [(e['root'], e['path']) for e in inv]
        if keys != sorted(set(keys)):
            raise ValueError('inventory not sorted/unique: ' + name)
        for e in inv:
            data = read(bases[e['root']], e['path'])
            if len(data) != e['size'] or digest(data) != e['sha256']:
                raise ValueError('authentication failed: ' + e['path'])
    inputs, outputs = manifests['inputs-manifest.json'], manifests['outputs-manifest.json']
    # The frozen candidate directory must contain exactly the inventoried files.
    cand = {e['path'][len(CANDIDATE) + 1:] for e in inputs
            if e['root'] == 'project' and e['path'].startswith(CANDIDATE + '/')}
    if files_under(PROJECT / CANDIDATE) != cand:
        raise ValueError('candidate directory differs from inventory')
    if digest(read(PROJECT, CANDIDATE + '/candidate.md')) != CANDIDATE_MD:
        raise ValueError('candidate.md hash differs from handoff')
    if digest(read(PROJECT, CANDIDATE + '/seal.json')) != CANDIDATE_SEAL:
        raise ValueError('candidate seal hash differs from handoff')
    own = {e['path'] for e in outputs} | OWN | {
        e['path'] for e in inputs if e['root'] == 'review'}
    if files_under(ROOT) != own:
        raise ValueError('review inventory mismatch: ' + repr(sorted(files_under(ROOT) ^ own)))

    def guard(event, args):
        if event == 'open':
            mode, flags = args[1:3]
            if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
                    isinstance(flags, int) and flags & (1 | 2 | 64 | 512 | 1024)):
                raise RuntimeError('write blocked')
        if event.startswith(('socket.', 'subprocess.')) or event in {
                'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.chmod',
                'os.link', 'os.symlink', 'os.system', 'os.truncate', 'os.utime',
                'os.exec', 'os.posix_spawn', 'os.fork'}:
            raise RuntimeError('blocked: ' + event)
    sys.addaudithook(guard)
    src = read(ROOT, 'checks/adversarial.py')
    scope = {'__name__': 'authenticated_adversarial_checks'}
    exec(compile(src, str(ROOT / 'checks/adversarial.py'), 'exec'), scope)
    replay = (json.dumps(scope['run'](), indent=1, sort_keys=True) + '\n').encode()
    if replay != read(ROOT, 'checks/adversarial.json'):
        raise ValueError('frozen receipt differs from deterministic replay')
    print(json.dumps({'status': 'PASS', 'inputs': len(inputs), 'outputs': len(outputs),
                      'candidate_files': len(cand), 'receipt_sha256': digest(replay),
                      'writes': 0, 'network': False,
                      'scope': 'Integrity and finite diagnostics; the proof verdict is in review.md.'},
                     indent=1, sort_keys=True))


if __name__ == '__main__':
    verify()
