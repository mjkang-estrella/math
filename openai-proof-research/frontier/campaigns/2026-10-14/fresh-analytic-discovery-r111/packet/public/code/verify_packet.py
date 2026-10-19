#!/usr/bin/env python3
"""Read-only exact-inventory integrity verifier. Not a mathematical gate."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
FROZEN='b266154b9b1b46ad7c4863bc23377d713f6da04e79e2fa3f7cb71415795a8f95'
SCREEN='07581061c85d60f82e76e479adaee8e5a7ceef07d09a1de1482840a9631c7e15'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def require(ok,msg):
    if not ok: raise ValueError(msg)
def digest(data): return hashlib.sha256(data).hexdigest()
def unique(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'duplicate JSON key')
        out[k]=v
    return out
def readjson(path): return json.loads(path.read_bytes(),object_pairs_hook=unique)
def safe(s):
    require(type(s) is str and s and '\\' not in s,'invalid path')
    p=PurePosixPath(s)
    require(not p.is_absolute() and str(p)==s and all(x not in ('','..','.') for x in s.split('/')),'unsafe path')
    return s
def hexhash(s,n=64): return type(s) is str and re.fullmatch('[0-9a-f]{'+str(n)+'}',s) is not None

def verify(root,expected):
    require(hexhash(expected),'invalid detached finalhash')
    require(not root.is_symlink() and root.is_dir(),'packet is not a real directory')
    files={}; dirs=[]
    for parent,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            f=Path(parent)/name; rel=f.relative_to(root).as_posix(); safe(rel); mode=f.lstat().st_mode
            require(not stat.S_ISLNK(mode),'symlink forbidden: '+rel)
            if stat.S_ISDIR(mode): dirs.append(rel)
            else:
                require(stat.S_ISREG(mode),'special file forbidden: '+rel)
                files[rel]=f
    require('manifest.json' in files,'manifest missing')
    require(digest(files['manifest.json'].read_bytes())==expected,'detached finalhash mismatch')
    m=readjson(files['manifest.json'])
    require(m.get('schema')=='t085e111-exact-packet-v1' and m.get('pin')==PIN,'manifest identity')
    require(m.get('status')=='UNRESOLVED_NO_NOMINEE','research disposition identity')
    require(type(m.get('files')) is list and type(m.get('directories')) is list,'inventory types')
    records={}
    for r in m['files']:
        require(type(r) is dict,'file record type'); s=safe(r.get('path'))
        require(s!='manifest.json' and s not in records,'duplicate/self manifest entry')
        require(type(r.get('bytes')) is int and r['bytes']>=0 and hexhash(r.get('sha256')),'file identity type')
        records[s]=r
    ds=[safe(s) for s in m['directories']]
    require(len(ds)==len(set(ds)),'duplicate directory')
    require(set(files)==set(records)|{'manifest.json'},'file inventory mismatch')
    require(set(dirs)==set(ds),'directory inventory mismatch')
    for s,r in records.items():
        data=files[s].read_bytes()
        require(len(data)==r['bytes'] and digest(data)==r['sha256'],'file identity mismatch: '+s)
    require(digest((root/'public/frozen-target.md').read_bytes())==FROZEN,'frozen target changed')
    require(digest((root/'public/pre-freeze-screen.md').read_bytes())==SCREEN,'prefreeze screen changed')
    fr=readjson(root/'public/freeze-receipt.json')
    require(fr['sha256']==FROZEN and fr['pre_freeze_screen_sha256']==SCREEN,'freeze receipt identity')
    t=readjson(root/'private/selected-tree-entries.json')
    require(t['pin']==PIN and t['complete_tree_entries']==13223 and t['truncated'] is False and t['complete_tree_sha256']==TREE,'complete tree identity')
    src=readjson(root/'private/source-provenance.json'); seen=set()
    for r in src:
        s=safe(r['path']); up=safe(r['upstream_path'])
        require(s not in seen,'duplicate raw source');seen.add(s)
        require(s=='private/upstream/'+up,'raw path mapping')
        require(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+up,'unpinned raw URL')
        data=(root/s).read_bytes(); blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(blob==r['git_blob']==t['entries'][up]['sha'] and t['entries'][up]['type']=='blob','Git blob identity')
        require(len(data)==r['bytes'] and digest(data)==r['sha256'],'raw receipt identity')
    require(set(t['entries'])=={r['upstream_path'] for r in src},'selected tree receipt coverage')
    require(seen=={s for s in records if s.startswith('private/upstream/')},'raw provenance coverage')
    primary=readjson(root/'private/primary/provenance.json'); covered=set()
    for r in primary:
        require(type(r['id']) is str and re.fullmatch('[a-z0-9.-]+',r['id']),'primary id')
        if r['status']=='failure':
            require(bool(r.get('error')),'failure without error');continue
        require(r['status']=='success','unknown retrieval status')
        pdf='private/primary/'+r['id']+'.pdf'; txt='private/primary/'+r['id']+'.txt'
        require(pdf not in covered,'duplicate primary');covered.update([pdf,txt])
        data=(root/pdf).read_bytes()
        require(digest(data)==r['sha256'] and len(data)==r['bytes'],'primary PDF identity')
        require(digest((root/txt).read_bytes())==r['text_sha256'],'primary extraction identity')
    require(covered=={s for s in records if s.startswith('private/primary/') and s.endswith(('.pdf','.txt'))},'primary provenance coverage')
    return {'integrity':'verified','mathematical_gate':False,'status':'UNRESOLVED_NO_NOMINEE','files':len(records)+1,'directories':len(dirs),'finalhash':expected}

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--packet',type=Path,required=True)
    a.add_argument('--expected-finalhash',required=True,help='Detached externally trusted SHA256; no fallback')
    q=a.parse_args()
    try: print(json.dumps(verify(q.packet,q.expected_finalhash),sort_keys=True))
    except (ValueError,KeyError,TypeError,OSError) as e:
        print('INTEGRITY_REJECT: '+str(e),file=sys.stderr);return 1
    return 0
if __name__=='__main__': sys.exit(main())
