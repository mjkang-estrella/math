#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only authentication before replay. No receipt generation or repair mode."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
ORIGINAL_SEAL = '75df70d930c3ccd57287e76a082dab1885bb844b0691132201ce2d4a199684e4'
ORIGINAL_CANDIDATE = 'e3f4c65e5eb0f35e9d19090e0ba897b27219a223795a0569319a3114cb3babcc'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(name):
    p = ROOT/name
    if p.is_symlink() or not p.resolve().is_relative_to(ROOT):
        raise ValueError('Unsafe input path: '+name)
    return p.read_bytes()


def verify():
    seal = json.loads(read('seal.json'))
    inventories = []
    for name in ['inputs-manifest.json','outputs-manifest.json']:
        raw = read(name)
        assert sha(raw)==seal['manifests'][name]['sha256']
        assert len(raw)==seal['manifests'][name]['size']
        entries=json.loads(raw)['files']
        names=[e['path'] for e in entries]
        assert names==sorted(set(names))
        for e in entries:
            data=read(e['path'])
            assert len(data)==e['size'] and sha(data)==e['sha256'],e['path']
        inventories.append(entries)
    expected={e['path'] for inv in inventories for e in inv}
    expected.update(['seal.json','inputs-manifest.json','outputs-manifest.json'])
    actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()}
    assert actual==expected,sorted(actual^expected)
    assert not any(p.is_symlink() for p in ROOT.rglob('*'))
    frozen='inputs/private/frozen-candidate/'
    assert sha(read(frozen+'seal.json'))==ORIGINAL_SEAL
    assert sha(read(frozen+'candidate.md'))==ORIGINAL_CANDIDATE

    def readonly(event,args):
        if event=='open':
            mode,flags=args[1:3]
            assert not (isinstance(mode,str) and any(c in mode for c in 'wax+'))
            assert not (isinstance(flags,int) and flags & (1|2|64|512|1024))
        assert not event.startswith(('socket.','subprocess.'))
        assert event not in {'os.remove','os.rename','os.rmdir','os.mkdir','os.chmod',
                             'os.link','os.symlink','os.system','os.truncate',
                             'os.utime','os.exec','os.posix_spawn'}
    sys.addaudithook(readonly)
    scope={'__name__':'authenticated_original_verifier',
           '__file__':str(ROOT/frozen/'verify.py')}
    with contextlib.redirect_stdout(io.StringIO()) as captured:
        exec(compile(read(frozen+'verify.py'),scope['__file__'],'exec'),scope)
        scope['verify']()
    assert captured.getvalue().encode()==read('candidate-verification.json')
    scope={'__name__':'authenticated_comparison_checks',
           '__file__':str(ROOT/'comparison_checks.py')}
    exec(compile(read('comparison_checks.py'),scope['__file__'],'exec'),scope)
    receipt=(json.dumps(scope['run'](),indent=2,sort_keys=True)+'\n').encode()
    assert receipt==read('comparison-receipt.json')
    print(json.dumps(dict(status='PASS',input_files=len(inventories[0]),
                          output_files=len(inventories[1]),writes=0,network=False,
                          frozen_candidate_authenticated=True,
                          frozen_candidate_verifier='PASS: 79 inputs / 12 outputs / 39 blobs',
                          comparison_receipt_sha256=sha(receipt),
                          verdict='TECHNICAL',
                          scope='Integrity and finite comparisons only; separate proof gate not assumed.'),
                     indent=2,sort_keys=True))

if __name__=='__main__':
    verify()
