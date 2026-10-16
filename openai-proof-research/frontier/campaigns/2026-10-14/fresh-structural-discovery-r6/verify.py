#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Read-only: authenticate all frozen bytes BEFORE any local code is executed."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
CONTROL={'seal.json','seal.sha256','inputs-manifest.json','outputs-manifest.json'}

def fail(message):raise RuntimeError(message)
def digest(b):return hashlib.sha256(b).hexdigest()
def safe(name):
    p=PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or str(p)!=name or name in ('','.'):fail('unsafe manifest path')
    f=ROOT.joinpath(*p.parts)
    if f.is_symlink() or any(q.is_symlink() for q in f.parents if q!=ROOT.parent):fail('symlink forbidden')
    return f

def authenticate(seal_hash):
    raw=(ROOT/'seal.json').read_bytes()
    if len(seal_hash)!=64 or digest(raw)!=seal_hash:fail('seal hash mismatch')
    seal=json.loads(raw)
    if seal['status']!='UNRESOLVED_NOT_NOMINATED':fail('scope/status mismatch')
    manifests=[]
    for name in ['inputs-manifest.json','outputs-manifest.json']:
        b=(ROOT/name).read_bytes();record=seal['manifests'][name]
        if len(b)!=record['size'] or digest(b)!=record['sha256']:fail('manifest authentication failed: '+name)
        manifests.append(json.loads(b))
    expected=set();counts=[]
    for kind,manifest in zip(['input','output'],manifests):
        if manifest['kind']!=kind:fail('manifest kind mismatch')
        counts.append(len(manifest['files']))
        for r in manifest['files']:
            name=r['path']
            if name in expected or name in CONTROL:fail('duplicate/control manifest entry')
            if name.startswith('inputs/')!=(kind=='input'):fail('input/output split mismatch')
            expected.add(name);f=safe(name)
            if not f.is_file():fail('missing regular file: '+name)
            b=f.read_bytes()
            if len(b)!=r['size'] or digest(b)!=r['sha256']:fail('file authentication failed: '+name)
    actual=set()
    for f in ROOT.rglob('*'):
        if f.is_symlink():fail('symlink forbidden')
        if f.is_file():actual.add(f.relative_to(ROOT).as_posix())
    if actual!=expected|CONTROL:fail('exact inventory mismatch')
    if (ROOT/'seal.sha256').read_text().strip()!=seal_hash:fail('detached hash mismatch')
    # These data are parsed only after their inventory authentication.
    tree=json.loads((ROOT/'inputs/private/context/sources/preprints-tree.json').read_text())
    if tree.get('truncated',False):fail('truncated source tree')
    paths={r['path']:r for r in tree['tree']};n=0
    for r in json.loads((ROOT/'retrieval-upstream.json').read_text()):
        b=safe(r['local']).read_bytes()
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if git!=r['git_blob'] or paths[r['path']]['sha']!=git:fail('pinned Git blob mismatch')
        want='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['path']
        if r['url']!=want or len(b)!=r['size'] or digest(b)!=r['sha256']:fail('source receipt mismatch')
        n+=1
    if n!=5:fail('unexpected pinned-source count')
    return counts,n,expected

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);a=ap.parse_args()
    counts,pins,expected=authenticate(a.seal_sha256)
    print(f'AUTHENTICATED {counts[0]} inputs, {counts[1]} outputs, {pins} pinned blobs; no local code executed before this point',flush=True)
    before={p:digest(safe(p).read_bytes()) for p in expected|CONTROL}
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
    for script,receipt in [('checks.py','checks-receipt.txt'),('generate_probe.py','exploration-receipt.txt')]:
        r=subprocess.run([sys.executable,'-B',str(ROOT/script)],cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
        if r.returncode or r.stderr:fail('authenticated finite replay failed: '+script+' '+r.stderr.decode(errors='replace'))
        if r.stdout!=(ROOT/receipt).read_bytes():fail('immutable receipt mismatch: '+receipt)
        print(f'REPLAY {script}: byte-identical receipt {digest(r.stdout)}',flush=True)
    authenticate(a.seal_sha256)
    if before!={p:digest(safe(p).read_bytes()) for p in expected|CONTROL}:fail('frozen file changed during replay')
    print('PASS_INTEGRITY_AND_FINITE_SUPPORT_ONLY_H_UNRESOLVED')

if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
