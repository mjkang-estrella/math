#!/usr/bin/env python3
"""Read-only verifier. Myeongjin Kang; no affiliation. MIT.

Authenticate this file with the README bootstrap BEFORE execution.
This program never creates/repairs manifests, seals, receipts, or caches.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys


def digest(data):return hashlib.sha256(data).hexdigest()


def require(condition,message):
    if not condition:raise ValueError(message)


def safe_path(root,name):
    q=PurePosixPath(name)
    require(not q.is_absolute() and '..' not in q.parts and str(q)==name,'unsafe path')
    require(bool(q.parts),'empty path')
    return root.joinpath(*q.parts)


def state(root):
    result={}
    for p in root.rglob('*'):
        require(not p.is_symlink(),'symlink rejected: '+str(p.relative_to(root)))
        if p.is_file():
            data=p.read_bytes();result[p.relative_to(root).as_posix()]=(len(data),digest(data))
    return result


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--seal-sha256',required=True)
    args=ap.parse_args()
    require(len(args.seal_sha256)==64 and all(c in '0123456789abcdef' for c in args.seal_sha256),'bad detached SHA256')
    root=Path(__file__).resolve().parent
    seal_bytes=(root/'seal.json').read_bytes()
    require(digest(seal_bytes)==args.seal_sha256,'detached seal mismatch')
    require((root/'seal.sha256').read_text()==args.seal_sha256+'  seal.json\n','convenience seal hash mismatch')
    seal=json.loads(seal_bytes)
    require(seal['format']=='fresh-analytic-r7-v1','unsupported seal')
    rows=[];counts={}
    for key in ['inputs','outputs']:
        meta=seal[key];p=safe_path(root,meta['path']);b=p.read_bytes()
        require(len(b)==meta['size'] and digest(b)==meta['sha256'],key+' manifest mismatch')
        obj=json.loads(b);require(obj['format']=='sha256-size-v1','unsupported manifest')
        counts[key]=len(obj['files']);rows.extend(obj['files'])
    names=[r['path'] for r in rows]
    require(len(names)==len(set(names)),'duplicate inventory path')
    for row in rows:
        p=safe_path(root,row['path']);require(p.is_file() and not p.is_symlink(),'missing file: '+row['path'])
        data=p.read_bytes()
        require(len(data)==row['size'] and digest(data)==row['sha256'],'file mismatch: '+row['path'])
    before=state(root)
    meta_names={'seal.json','seal.sha256',seal['inputs']['path'],seal['outputs']['path']}
    require(set(before)==set(names)|meta_names,'file membership mismatch')
    # Re-authenticate every raw source against the independently inventoried path tree.
    tree=json.loads((root/'inputs/private/context/sources/preprints-tree.json').read_bytes())
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    retrieval=json.loads((root/'source-retrieval.json').read_bytes())
    for row in retrieval:
        data=safe_path(root,'inputs/private/upstream/'+row['path']).read_bytes()
        h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(h==row['git_blob_sha1']==blobs[row['path']],'pinned git blob mismatch')
        require(len(data)==row['size'] and digest(data)==row['sha256'],'retrieval record mismatch')
        require('/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in row['url'],'unpinned URL')
    # All bytes, code, receipts and membership have been authenticated at this point.
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    result=subprocess.run([sys.executable,'-B',str(root/'checks.py')],cwd=root,
                          env=env,capture_output=True,timeout=120)
    require(state(root)==before,'checker changed package')
    require(result.returncode==0 and not result.stderr,'checker execution failed')
    require(result.stdout==(root/'checks-receipt.txt').read_bytes(),'frozen receipt mismatch')
    print(json.dumps({'status':'PASS_AUTHENTICATION_AND_EXACT_SUPPORT_ONLY',
                      'input_files':counts['inputs'],'output_files':counts['outputs'],
                      'pinned_source_blobs':len(retrieval),'receipt_byte_identical':True,
                      'package_unchanged':True,
                      'mathematical_status':'proposed complete F; independent proof and contribution reviews pending'},
                     sort_keys=True,indent=2))


if __name__=='__main__':
    try:main()
    except Exception as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
