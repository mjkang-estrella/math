#!/usr/bin/env python3
# Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
# Original r27 read-only verifier; no subprocess, network, repair, or resealing.
import argparse, hashlib, json, re
from pathlib import Path, PurePosixPath

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def digest(b): return hashlib.sha256(b).hexdigest()
def safe(s):
    q=PurePosixPath(s)
    if not s or q.is_absolute() or '..' in q.parts or str(q)!=s:
        raise ValueError('unsafe relative path')
    return q

def verify(root,anchor):
    if not re.fullmatch('[0-9a-f]{64}',anchor): raise ValueError('invalid external anchor')
    if root.is_symlink() or not root.is_dir(): raise ValueError('unsafe root')
    manifest=root/'output-manifest.json'
    if manifest.is_symlink() or not manifest.is_file(): raise ValueError('missing regular manifest')
    raw=manifest.read_bytes()
    if digest(raw)!=anchor: raise ValueError('external anchor mismatch')
    data=json.loads(raw)
    if data['source_pin']!=PIN: raise ValueError('pin mismatch')
    files={};dirs=set()
    for q in root.rglob('*'):
        if q.is_symlink(): raise ValueError('symlink forbidden')
        name=q.relative_to(root).as_posix()
        if q.is_dir(): dirs.add(name)
        elif q.is_file():
            if name!='output-manifest.json': files[name]=q
        else: raise ValueError('special file forbidden')
    expected=data['files']
    if list(expected)!=sorted(expected): raise ValueError('unsorted file inventory')
    if set(files)!=set(expected) or dirs!=set(data['directories']):
        raise ValueError('exact membership mismatch')
    for name, rec in expected.items():
        safe(name); b=files[name].read_bytes()
        if len(b)!=rec['bytes'] or digest(b)!=rec['sha256']:
            raise ValueError('payload identity mismatch: '+name)
    freeze=json.loads((root/'freeze-receipt.json').read_bytes())
    if digest((root/'original-scope.md').read_bytes())!=freeze['scope_sha256']:
        raise ValueError('frozen scope mismatch')
    for name,sha in freeze['prefreeze_inputs'].items():
        safe(name)
        if digest((root/name).read_bytes())!=sha: raise ValueError('pre-freeze identity mismatch')
    src=json.loads((root/'source-receipt.json').read_bytes())
    selected=json.loads((root/'input-manifest.json').read_bytes())['selected_pinned_tree_records']
    table={r['path']:r['sha'] for r in selected}
    for r in src:
        safe(r['local']);b=(root/r['local']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if blob!=r['git_blob'] or table.get(r['path'])!=blob or digest(b)!=r['sha256'] or len(b)!=r['bytes']:
            raise ValueError('pinned source identity mismatch')
        if '/'+PIN+'/' not in r['url']: raise ValueError('unpinned source URL')
    prim=json.loads((root/'primary-receipt.json').read_bytes())
    for r in json.loads((root/'private/primary/receipts.json').read_bytes()):
        prim.append(dict(r,local='private/primary/'+r['name']+'.pdf'))
    for r in prim:
        safe(r['local']);b=(root/r['local']).read_bytes()
        if not b.startswith(b'%PDF') or digest(b)!=r['sha256'] or len(b)!=r['bytes']:
            raise ValueError('primary PDF identity mismatch')
    for r in json.loads((root/'input-manifest.json').read_bytes())['snapshots']:
        safe(r['local']);b=(root/r['local']).read_bytes()
        if digest(b)!=r['sha256'] or len(b)!=r['bytes']: raise ValueError('snapshot mismatch')
    return {'status':'IDENTITY_ONLY','payloads':len(files),'directories':len(dirs),
            'pinned_blobs':len(src),'primary_pdfs':len(prim),
            'scope_sha256':freeze['scope_sha256'],'candidate_sha256':digest((root/'candidate.md').read_bytes()),
            'mathematical_or_contribution_verdict':False}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True)
    ap.add_argument('--root',type=Path,default=Path(__file__).parent)
    args=ap.parse_args()
    try: print(json.dumps(verify(args.root,args.anchor),indent=2,sort_keys=True))
    except (ValueError,KeyError,TypeError,OSError,json.JSONDecodeError) as e:
        ap.exit(1,'VERIFY_REJECTED: '+str(e)+'\n')
if __name__=='__main__': main()
