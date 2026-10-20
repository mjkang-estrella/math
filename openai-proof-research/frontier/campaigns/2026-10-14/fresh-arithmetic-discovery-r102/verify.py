#!/usr/bin/env python3
"""Read-only r102 artifact verifier; all three detached anchors are required.
Artifact verification is not mathematical correctness or contribution review.
"""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath

OUTSIDE={'FINAL.json','MANIFEST.json','REPORT.md'}
TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
SCOPE='fc1e349511e87ebd6a0ba0c1533b2c8a81e5fca100e30e9ef2ad7cf5915f002b'
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise ValueError(msg)
def unique(items):
    d={}
    for k,v in items:
        require(k not in d,'duplicate JSON key: '+k); d[k]=v
    return d
def readjson(p): return json.loads(p.read_text(),object_pairs_hook=unique)
def safe(s):
    p=PurePosixPath(s)
    require(s and not p.is_absolute() and '..' not in p.parts and '.' not in p.parts and str(p)==s,'unsafe relative path')
    return s
def inventory(root):
    require(stat.S_ISDIR(root.lstat().st_mode),'root is not a real directory')
    fs={}; ds={}
    for base,dirs,files in os.walk(root,followlinks=False):
        for name in sorted(dirs+files):
            p=Path(base)/name; rel=p.relative_to(root).as_posix(); st=p.lstat()
            require(not stat.S_ISLNK(st.st_mode),'symlink: '+rel)
            mode=stat.S_IMODE(st.st_mode)
            if stat.S_ISDIR(st.st_mode): ds[rel]=mode
            else:
                require(stat.S_ISREG(st.st_mode),'special file: '+rel)
                if rel not in OUTSIDE: fs[rel]={'bytes':st.st_size,'mode':mode,'sha256':digest(p)}
    return {'files':fs,'directories':ds,'root_mode':stat.S_IMODE(root.lstat().st_mode)}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True)
    for n in ['final','manifest','report']: ap.add_argument('--'+n+'-sha256',required=True)
    a=ap.parse_args();root=Path(a.root)
    for name,key in [('FINAL.json','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:
        h=getattr(a,key+'_sha256');require(re.fullmatch('[0-9a-f]{64}',h) is not None,'anchor must be full SHA256')
        p=root/name;require(stat.S_ISREG(p.lstat().st_mode),'anchor is not regular file: '+name)
        require(digest(p)==h,'external anchor mismatch: '+name)
    final=readjson(root/'FINAL.json');m=readjson(root/'MANIFEST.json')
    require(final['manifest_sha256']==a.manifest_sha256,'FINAL manifest binding')
    require(final['report_sha256']==a.report_sha256,'FINAL outside REPORT binding')
    require(final['scope_sha256']==SCOPE==digest(root/'public/SCOPE.md'),'frozen scope binding')
    require(final['proof_sha256']==digest(root/'public/PROOF.md'),'proof binding')
    require(final['mathematical_gates']=='UNREVIEWED','unexpected gate assertion')
    for s in list(m['files'])+list(m['directories']):safe(s)
    got=inventory(root)
    require(got=={k:m[k] for k in got},'exact payload inventory/content/mode mismatch')
    require({p.name for p in root.iterdir() if p.name in OUTSIDE}==OUTSIDE,'missing outside file')
    for binding in ['private/context/bindings.json','private/history/bindings.json']:
        for x in readjson(root/binding):
            require(digest(root/safe(x['copy']))==x['sha256'],'copied original binding: '+x['copy'])
    treepath=root/'private/context/03-preprints-tree.json'
    require(digest(treepath)==TREE_SHA,'complete tree anchor')
    tree=readjson(treepath)
    require(len(tree['tree'])==13223 and tree['truncated'] is False,'complete tree structure')
    index={x['path']:x for x in tree['tree']}
    bodies=readjson(root/'private/acquisitions/register.json');count=0
    for x in bodies:
        require(x['status']=='authenticated','unresolved source acquisition')
        p=root/safe(x['local']);b=p.read_bytes();meta=index[x['path']]
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(blob==meta['sha']==x['git_blob']==x['expected_blob'],'pinned Git blob')
        require(len(b)==meta['size']==x['bytes'] and digest(p)==x['sha256'],'pinned size/SHA256')
        require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'],'pinned URL')
        count+=1
    require(readjson(root/'public/freeze.json')['scope_sha256']==SCOPE,'freeze record')
    print(json.dumps({'artifact_verification':'PASS','payload_files':len(got['files']),'payload_directories':len(got['directories']),'pinned_bodies':count,'mathematical_gate':False,'scope_sha256':SCOPE,'limits':'Exact r102 root and detached anchors; originals are represented by copies. No external-original mutation audit, syscall sandbox, mathematical correctness, contribution or priority certification.'},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
