#!/usr/bin/env python3
"""Read-only authentication and finite-support replay. MIT, Myeongjin Kang."""
import sys
sys.dont_write_bytecode=True
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT=Path(__file__).resolve().parent
REV='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
F_SEAL='80f72efab2af1c25bb440a49fcaacd5410601d328b83c0f59055be65958ae7bc'
SCOPE='d8686a39d756a2aee505382600106c0aa6f821f5a9496016767752038ab634a6'
META={'seal.json','seal.sha256','inputs-manifest.json','outputs-manifest.json'}

def require(ok,message):
    if not ok:raise ValueError(message)

def sha(b):return hashlib.sha256(b).hexdigest()
def safe(p):
    require(isinstance(p,str),'path must be text')
    q=PurePosixPath(p)
    require(p==str(q) and not q.is_absolute() and all(x not in ('','.', '..') for x in q.parts),'unsafe path '+p)
    return p

def read(p):
    f=ROOT/safe(p)
    require(f.is_file() and not f.is_symlink(),'missing file or symlink '+p)
    return f.read_bytes()

def check_entry(e):
    p=safe(e['path']); b=read(p)
    require(type(e['size']) is int and e['size']>=0,'invalid size '+p)
    require(len(b)==e['size'] and sha(b)==e['sha256'],'payload hash/size mismatch '+p)
    return p

def validate():
    require(len(sys.argv)==2 and re.fullmatch('[0-9a-f]{64}',sys.argv[1]) is not None,'supply external lowercase seal SHA256')
    anchor=sys.argv[1]
    sb=read('seal.json');require(sha(sb)==anchor,'detached seal anchor mismatch')
    require(read('seal.sha256')==(anchor+'  seal.json\n').encode(),'convenience seal file mismatch')
    seal=json.loads(sb);require(seal['revision']==REV,'wrong upstream revision')
    paths=set()
    counts={}
    for kind in ('inputs','outputs'):
        e=seal[kind];require(e['path']==kind+'-manifest.json','wrong inventory path')
        b=read(e['path']);require(len(b)==e['size'] and sha(b)==e['sha256'],'inventory anchor mismatch '+kind)
        m=json.loads(b);require(m['format']=='sha256-size-v1','inventory format')
        counts[kind]=len(m['files'])
        for e in m['files']:
            p=check_entry(e);require(p not in paths and p not in META,'duplicate or reserved inventory member '+p);paths.add(p)
            require((p.startswith('inputs/'))==(kind=='inputs'),'wrong inventory classification '+p)
    expected=paths|META
    actual=set();dirs=set()
    for f in ROOT.rglob('*'):
        require(not f.is_symlink(),'symlink in package '+str(f.relative_to(ROOT)))
        p=str(f.relative_to(ROOT))
        if f.is_file():actual.add(p)
        elif f.is_dir():dirs.add(p)
        else:raise ValueError('nonregular object '+p)
    require(actual==expected,'exact file membership mismatch')
    expected_dirs={str(q) for p in expected for q in PurePosixPath(p).parents if str(q)!='.'}
    require(dirs==expected_dirs,'exact directory membership mismatch')
    require(sha(read('original-scope.md'))==SCOPE,'frozen scope changed')
    require(json.loads(read('scope-freeze.json'))['scope_sha256']==SCOPE,'scope freeze anchor mismatch')

    # Preserved predecessor: authenticate its external seal and all nested payloads;
    # do not execute predecessor code.
    prefix='inputs/private/frozen-r7/'
    fsb=read(prefix+'seal.json');require(sha(fsb)==F_SEAL,'preserved F seal mismatch')
    fs=json.loads(fsb);fpaths=set()
    for kind in ('inputs','outputs'):
        e=fs[kind];b=read(prefix+e['path'])
        require(len(b)==e['size'] and sha(b)==e['sha256'],'F inventory mismatch')
        for e in json.loads(b)['files']:
            p=safe(e['path']);bb=read(prefix+p)
            require(len(bb)==e['size'] and sha(bb)==e['sha256'],'F payload mismatch '+p);fpaths.add(p)
    require({p[len(prefix):] for p in actual if p.startswith(prefix)}==fpaths|META,'F exact membership mismatch')
    require(read(prefix+'seal.sha256')==(F_SEAL+'  seal.json\n').encode(),'F detached convenience file mismatch')

    tree=json.loads(read('inputs/private/context/sources/preprints-tree.json'))
    require(tree['truncated'] is False,'truncated upstream tree forbidden')
    blobs={e['path']:e for e in tree['tree'] if e['type']=='blob'}
    sources=json.loads(read(prefix+'source-retrieval.json'))
    require(len(sources)==13,'pinned source count changed')
    for e in sources:
        p=safe(e['path']);b=read(prefix+'inputs/private/upstream/'+p)
        require(len(b)==e['size'] and sha(b)==e['sha256'],'source SHA256/size mismatch '+p)
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(p in blobs and git==blobs[p]['sha']==e['git_blob_sha1'],'pinned Git blob mismatch '+p)
        require(e['url']=='https://raw.githubusercontent.com/openai/math/'+REV+'/'+p,'unpinned source URL '+p)
    return anchor,counts,len(sources)

try:
    anchor,counts,blobs=validate()
    # All code and receipts authenticated above before replay. -B plus the explicit
    # environment prevents bytecode writes. No inventory or receipt regeneration.
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    p=subprocess.run([sys.executable,'-B',str(ROOT/'checks.py')],cwd=ROOT,env=env,capture_output=True,timeout=60)
    require(p.returncode==0,'finite checker failed')
    require(p.stderr==b'','unexpected checker stderr')
    require(p.stdout==read('checks-receipt.json'),'checker receipt mismatch')
    print(json.dumps({'status':'PASS_AUTHENTICATION_AND_EXACT_FINITE_SUPPORT_ONLY','seal_sha256':anchor,'inputs':counts['inputs'],'outputs':counts['outputs'],'pinned_blobs':blobs,'mathematics':'PROPOSED_COMPLETE_PENDING_INDEPENDENT_PROOF_AND_CONTRIBUTION_GATES','counted':False},sort_keys=True))
except Exception as e:
    print('FAIL: '+str(e),file=sys.stderr)
    sys.exit(1)
