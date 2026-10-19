#!/usr/bin/env python3
"""Read-only artifact verifier. No mathematical or contribution verdict."""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path,PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA256='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def need(v,msg):
    if not v: raise ValueError(msg)
def pairs(items):
    d={}
    for k,v in items:
        need(k not in d,'duplicate JSON key');d[k]=v
    return d
def js(b):return json.loads(b,object_pairs_hook=pairs)
def sha(b):return hashlib.sha256(b).hexdigest()
def regular(p):
    s=p.lstat();need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'not single-link regular file: '+str(p));return s
def rel(s):
    p=PurePosixPath(s);need(not p.is_absolute() and '..' not in p.parts and str(p)==s,'unsafe relative path');return s

def verify(root,final,tree):
    need(not root.is_symlink(),'packet root symlink');root=root.resolve(strict=True)
    need(root.is_dir(),'packet not directory')
    regular(final);need(not final.resolve().is_relative_to(root),'FINAL must be detached')
    token=final.read_text();need(re.fullmatch('[0-9a-f]{64}\n?',token) is not None,'bad detached FINAL')
    man=root/'MANIFEST.json';ms=regular(man);need(stat.S_IMODE(ms.st_mode)==0o644,'manifest mode')
    raw=man.read_bytes();need(sha(raw)==token.strip(),'detached manifest digest mismatch');m=js(raw)
    need(m['schema']=='r127-exact-packet-v1' and m['pin']==PIN,'manifest contract')
    actual_files={};actual_dirs={'.':stat.S_IMODE(root.stat().st_mode)}
    for base,dirs,files in os.walk(root,followlinks=False):
        for name in dirs:
            p=Path(base)/name;s=p.lstat();need(stat.S_ISDIR(s.st_mode),'non-directory entry');actual_dirs[p.relative_to(root).as_posix()]=stat.S_IMODE(s.st_mode)
        for name in files:
            p=Path(base)/name;s=regular(p);k=p.relative_to(root).as_posix()
            if k=='MANIFEST.json':continue
            b=p.read_bytes();actual_files[k]={'sha256':sha(b),'bytes':len(b),'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink}
    for k in m['files']:rel(k)
    for k in m['directories']:rel(k)
    need(actual_files==m['files'],'exact file inventory/content/type/mode/link mismatch')
    need(actual_dirs==m['directories'],'exact directory inventory/mode mismatch')
    traw=tree.read_bytes();need(sha(traw)==TREE_SHA256,'complete-tree digest mismatch');t=js(traw)
    need(t['truncated'] is False and len(t['tree'])==13223,'incomplete tree')
    idx={x['path']:x for x in t['tree']};need(len(idx)==13223,'duplicate canonical tree paths')
    records=js((root/'private/canonical.json').read_bytes());seen=set()
    for r in records:
        c=r['canonical'];p=c['path'];need(p not in seen,'duplicate source');seen.add(p)
        need(idx.get(p)==c,'full canonical record mismatch')
        need(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p,'wrong pinned raw URL')
        need(r['local']=='private/upstream/'+p,'wrong local source path')
        b=(root/rel(r['local'])).read_bytes()
        need(len(b)==c['size'] and sha(b)==r['sha256'],'source bytes/SHA256')
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'],'Git blob mismatch')
    for r in js((root/'private/history.json').read_bytes()):
        b=(root/rel(r['local'])).read_bytes();need(sha(b)==r['sha256'] and len(b)==r['bytes'],'history receipt mismatch')
    ps=js((root/'private/primary/acquisition.json').read_bytes())
    for r in ps:
        need('error' not in r and r['extraction_exit']==0,'primary acquisition failure')
        name=rel(r['name']);need('/' not in name,'bad primary name')
        b=(root/'private/primary'/f'{name}.pdf').read_bytes();txt=(root/'private/primary'/f'{name}.txt').read_bytes()
        need(len(b)==r['bytes'] and sha(b)==r['sha256'] and sha(txt)==r['text_sha256'],'primary receipt mismatch')
    for r in js((root/'private/search-receipts.json').read_bytes()):
        need(r['retained'] is False and not (root/rel(r['path'])).exists(),'search retention mismatch')
        need(r['exit']==0 and r['stderr']=='','search failure')
    state=js((root/'private/session-limits.json').read_bytes())
    need(state['status']=='PREFREEZE' and state['frozen_target'] is None and state['nominee'] is None,'wrong archive status')
    return dict(artifact_inventory='verified',files=len(actual_files),directories=len(actual_dirs),canonical_bodies=len(records),primary_pairs=len(ps),mathematical_verdict=None)

def main():
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--packet',type=Path,required=True);a.add_argument('--finalhash',type=Path,required=True);a.add_argument('--tree',type=Path,required=True);x=a.parse_args()
    try:print(json.dumps(verify(x.packet,x.finalhash,x.tree),sort_keys=True))
    except Exception as e:print('REJECT: '+str(e),file=sys.stderr);return 1
    return 0
if __name__=='__main__':sys.exit(main())
