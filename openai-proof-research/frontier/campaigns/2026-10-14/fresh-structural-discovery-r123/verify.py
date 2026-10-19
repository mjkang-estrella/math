#!/usr/bin/env python3
"""Read-only archive authentication. No mathematical inference or gate."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREEHASH='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def deny_mutation(event,args):
    if event=='open':
        mode=args[1]; flags=args[2]
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('READ_ONLY: write denied')
    if event in {'os.remove','os.rmdir','os.mkdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.truncate','os.utime','subprocess.Popen','os.system','os.exec','os.posix_spawn','socket.__new__','os.fork'}:
        raise PermissionError('READ_ONLY: mutation/process/network denied')
sys.addaudithook(deny_mutation)

def require(ok,msg):
    if not ok: raise ValueError(msg)
def digest(b): return hashlib.sha256(b).hexdigest()
def safe_rel(s):
    require(isinstance(s,str) and s and '\\' not in s and '\x00' not in s,'unsafe relative path')
    p=PurePosixPath(s)
    require(not p.is_absolute() and all(v not in ('','.','..') for v in s.split('/')),'unsafe relative path')
    return s

def read(p):
    st=p.lstat(); require(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular or hardlinked file: '+str(p))
    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK)
    try:
        fs=os.fstat(fd); require(stat.S_ISREG(fs.st_mode) and fs.st_nlink==1 and (fs.st_dev,fs.st_ino)==(st.st_dev,st.st_ino),'file changed/type error')
        with os.fdopen(fd,'rb',closefd=False) as f: b=f.read()
        require(len(b)==fs.st_size,'size changed')
        return b
    finally: os.close(fd)
def scan(root):
    require(stat.S_ISDIR(root.lstat().st_mode),'packet root not directory')
    files={}; dirs=[]
    def visit(p):
        for e in sorted(os.scandir(p),key=lambda x:x.name):
            q=Path(e.path); rel=q.relative_to(root).as_posix(); safe_rel(rel); s=q.lstat()
            if stat.S_ISDIR(s.st_mode): dirs.append(rel); visit(q)
            else:
                require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular payload: '+rel)
                b=read(q);files[rel]={'sha256':digest(b),'bytes':len(b),'mode':stat.S_IMODE(s.st_mode)}
    visit(root); return files,sorted(dirs)
def load(p): return json.loads(read(p))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True)
    ap.add_argument('--probe',choices=['write','process'])
    a=ap.parse_args()
    for h in [a.finalhash,a.reporthash]: require(re.fullmatch('[0-9a-f]{64}',h) is not None,'malformed detached anchor')
    root=Path(os.path.abspath(a.root))
    for p in [root,*root.parents]: require(stat.S_ISDIR(p.lstat().st_mode),'root ancestry not real directory')
    finalbytes=read(root/'FINAL.json');require(digest(finalbytes)==a.finalhash,'DETACHED FINAL mismatch');final=json.loads(finalbytes)
    require(final['schema']=='r123-prefreeze-v1' and final['pin']==PIN and final['frozen_target'] is None and final['nomination'] is False,'FINAL scope mismatch')
    report=read(root/'REPORT.md');require(digest(report)==a.reporthash==final['report_sha256'],'DETACHED REPORT mismatch')
    require(set(final['code'])=={'verify.py','run_controls.py'},'code membership')
    require(Path(os.path.abspath(__file__))==root/'verify.py','must execute OWN verifier')
    for name,h in final['code'].items():require(digest(read(root/name))==h,'code hash mismatch: '+name)
    manbytes=read(root/'MANIFEST.json');require(digest(manbytes)==final['manifest_sha256'],'manifest hash mismatch');man=json.loads(manbytes)
    require(set(man)=={'schema','files','directories'} and man['schema']=='exact-packet-v1','manifest schema')
    for s in list(man['files'])+man['directories']:safe_rel(s)
    files,dirs=scan(root/'packet');require(files==man['files'],'exact payload files/hash/mode mismatch');require(dirs==man['directories'],'exact directory membership mismatch')
    require(files['public/report.md']['sha256']==final['public_report_sha256'],'public report hash mismatch')
    treeb=read(root/'packet/private/context/preprints-tree.json');require(digest(treeb)==TREEHASH,'canonical tree hash mismatch');tree=json.loads(treeb)
    require(tree['truncated'] is False and len(tree['tree'])==13223,'complete tree required')
    entries={v['path']:v for v in tree['tree']};require(len(entries)==13223,'duplicate canonical paths')
    records=load(root/'packet/public/source-register.json');seen=set()
    for r in records:
        path=safe_rel(r['path']);require(path not in seen,'duplicate source');seen.add(path)
        canon=entries[path];require(canon==r['canonical_record'] and canon['type']=='blob','full canonical record mismatch')
        require(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,'pinned raw URL mismatch')
        require(r['local']=='private/upstream/'+path,'source local mapping mismatch')
        b=read(root/'packet'/safe_rel(r['local']));blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(blob==r['git_blob']==canon['sha'] and len(b)==r['bytes']==canon['size'] and digest(b)==r['sha256'],'canonical bytes mismatch')
        require(re.findall(rb'\\label\{([^}]+)\}',b)==[x.encode() for x in r['labels']],'label register mismatch')
    hist=load(root/'packet/public/history-register.json')
    for r in hist: require(digest(read(root/'packet'/safe_rel(r['local'])))==r['sha256'],'history hash mismatch')
    prim=load(root/'packet/public/primary-register.json')
    for r in prim:
        for art in r.get('artifacts',[]):require(digest(read(root/'packet'/safe_rel(art['local'])))==art['sha256'],'primary artifact mismatch')
    for r in load(root/'packet/public/search-register.json'):
        require(digest(read(root/'packet'/safe_rel(r['path_list'])))==r['path_list_sha256'],'search path list mismatch')
    if a.probe:
        try:
            if a.probe=='write':
                with open(root/'READ_ONLY_PROBE','wb') as f: f.write(b'forbidden')
            else: os.system('true')
        except PermissionError as e:
            require('READ_ONLY:' in str(e),'unexpected probe error');print(json.dumps({'probe':a.probe,'denied':True}));return
        raise ValueError('read-only probe unexpectedly succeeded')
    print(json.dumps({'integrity':'authenticated','payload_files':len(files),'directories':len(dirs),'canonical_sources':len(records),'history_copies':len(hist),'primary_records':len(prim),'frozen_target':None,'nomination':False,'mathematical_gate':False},sort_keys=True))

if __name__=='__main__':
    try: main()
    except Exception as e: print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
