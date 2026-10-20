#!/usr/bin/env python3
"""Read-only exact-packet verification using three externally supplied hashes."""
import argparse
import hashlib
import json
import os
from pathlib import Path

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,why):
    if not ok: raise ValueError(why)
def verify(root, anchors):
    root=Path(root)
    require(not root.is_symlink(),'symlink root')
    packet=root/'packet'
    require(packet.is_dir() and not packet.is_symlink(),'bad packet directory')
    for name,rel in [('final','packet/FINAL.json'),('manifest','packet/MANIFEST.json'),('report','REPORT.md')]:
        p=root/rel
        require(p.is_file() and not p.is_symlink(),'bad '+rel)
        require(sha(p)==anchors[name],name+' anchor mismatch')
    manifest=json.loads((packet/'MANIFEST.json').read_text())
    expected=manifest['files']; seen={};dirs=[]
    for base,children,files in os.walk(packet,followlinks=False):
        for n in children:
            p=Path(base,n);require(not p.is_symlink(),'symlink directory')
            dirs.append(p.relative_to(packet).as_posix())
        for n in files:
            p=Path(base,n);require(p.is_file() and not p.is_symlink(),'nonregular payload')
            rel=p.relative_to(packet).as_posix()
            if rel=='MANIFEST.json':continue
            seen[rel]={'bytes':p.stat().st_size,'sha256':sha(p)}
    require(seen==expected,'exact payload mismatch')
    require(sorted(dirs)==manifest['directories'],'exact directory mismatch')
    final=json.loads((packet/'FINAL.json').read_text())
    require(final['status']=='PREFREEZE_NO_NOMINEE','unexpected status')
    require(final['candidate_frozen'] is False,'unexpected candidate freeze')
    treefile=packet/'private/context/sources/preprints-tree.json'
    require(sha(treefile)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','complete tree anchor')
    tree=json.loads(treefile.read_text())
    require(len(tree['tree'])==13223 and tree['truncated'] is False,'complete tree extent')
    entries={x['path']:x for x in tree['tree']}
    acquisition=json.loads((packet/'private/sources/acquisition.json').read_text())
    for item in acquisition:
        rel=item['path'];b=(packet/'private/sources'/rel).read_bytes();e=entries[rel]
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(e['type']=='blob' and e['size']==len(b) and e['sha']==blob,'pinned blob '+rel)
        require(item['sha256']==hashlib.sha256(b).hexdigest(),'source sha256 '+rel)
        require(item['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+rel,'unpinned URL')
    return {'verified':True,'payload_files':len(seen),'directories':len(dirs),
            'pinned_blobs':len(acquisition),'status':final['status'],'mathematical_gate':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('root')
    for k in ['final','manifest','report']:ap.add_argument('--'+k+'-sha256',required=True)
    a=ap.parse_args()
    try:print(json.dumps(verify(a.root,{k:getattr(a,k+'_sha256') for k in ['final','manifest','report']}),sort_keys=True))
    except (OSError,ValueError,KeyError,TypeError) as e:
        print(json.dumps({'verified':False,'error':str(e)}));raise SystemExit(1)
