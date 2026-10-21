"""Read-only byte/membership verifier. Explicit detached anchors are mandatory.

No network, subprocess, repair, resealing or mathematical assertions.
Reduced controls have independent membership and do not authenticate originals.
"""
import argparse, hashlib, json, os, stat
from pathlib import Path

TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def digest(b): return hashlib.sha256(b).hexdigest()
def require(ok,message):
    if not ok: raise ValueError(message)
def read(p):
    st=p.lstat()
    require(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'not a regular single-link file: '+str(p))
    return p.read_bytes()
def inventory(root):
    files={};dirs=[]
    require(root.is_dir() and not root.is_symlink(),'invalid root')
    for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
        ds.sort();fs.sort()
        for d in ds:
            p=Path(base)/d
            require(stat.S_ISDIR(p.lstat().st_mode),'non-directory/symlink: '+str(p))
            dirs.append(p.relative_to(root).as_posix())
        for f in fs:
            p=Path(base)/f;b=read(p)
            files[p.relative_to(root).as_posix()]={'bytes':len(b),'sha256':digest(b)}
    return files,sorted(dirs)

def verify(root,anchors):
    for name,h in anchors.items():
        require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'invalid detached hash')
        require(digest(read(root/name))==h,'detached anchor mismatch: '+name)
    outer=json.loads(read(root/'MANIFEST.json'))
    require(outer['kind'] in ['original-r113','reduced-control'],'unknown envelope kind')
    require(set(outer['files'])=={'FINAL.json','REPORT.md','packet/MANIFEST.json'},'outer coverage')
    for name,row in outer['files'].items():
        b=read(root/name)
        require(row=={'bytes':len(b),'sha256':digest(b)},'outer binding: '+name)
    inner=json.loads(read(root/'packet/MANIFEST.json'))
    require(inner['kind']==outer['kind'],'manifest kinds differ')
    files,dirs=inventory(root)
    expected={('packet/'+k):v for k,v in inner['files'].items()}
    for name in ['FINAL.json','REPORT.md','MANIFEST.json','packet/MANIFEST.json']:
        b=read(root/name);expected[name]={'bytes':len(b),'sha256':digest(b)}
    require(files==expected,'exact membership or payload bytes differ')
    require(dirs==sorted(['packet']+['packet/'+d for d in inner['directories']]),'directory membership differs')
    canonical=0
    if outer['kind']=='original-r113':
        p=root/'packet';tb=read(p/'private/source/preprints-tree.json')
        require(digest(tb)==TREE_SHA,'complete tree SHA')
        tree=json.loads(tb);require(tree['truncated'] is False and len(tree['tree'])==13223,'complete tree shape')
        entries={x['path']:x for x in tree['tree']}
        rows=json.loads(read(p/'private/source/authentication.json'))
        require(len(rows)==35 and len({x['path'] for x in rows})==35,'canonical receipt cardinality')
        for row in rows:
            path=row['path'];e=entries[path]
            require(row['local']=='private/source/'+path,'canonical local path')
            b=read(p/row['local']);g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            require(e['type']=='blob' and e['size']==row['bytes']==len(b),'canonical size/type')
            require(e['sha']==row['git_blob']==g,'canonical Git blob')
            require(row['sha256']==digest(b),'canonical SHA256')
            require(row['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,'canonical pinned URL')
            canonical+=1
        h=json.loads(read(p/'private/history/authentication.json'))
        for row in h['records']:
            b=read(p/row['copy'])
            require(len(b)==row['bytes'] and digest(b)==row['sha256'],'retained original/excerpt copy binding')
    return {'kind':outer['kind'],'files':len(files),'directories':len(dirs),
            'canonical_source_blobs':canonical,
            'scope':'bytes and exact membership only; no mathematical or isolation gate'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    for x in ['final','manifest','report']:ap.add_argument('--'+x+'-sha',required=True)
    a=ap.parse_args()
    try:
        result=verify(a.root,{'FINAL.json':a.final_sha,'MANIFEST.json':a.manifest_sha,'REPORT.md':a.report_sha})
    except (ValueError,KeyError,OSError,TypeError) as e:
        print('REJECT:',e);return 1
    print(json.dumps(result,sort_keys=True));return 0

if __name__=='__main__':raise SystemExit(main())
