#!/usr/bin/env python3
"""Read-only r126 archive verifier. Integrity only; no mathematical gate. MIT."""
import sys
sys.dont_write_bytecode = True
import os, stat, json, hashlib, argparse
from pathlib import Path

def audit(event,args):
    if event=='open':
        mode=args[1] or ''; flags=args[2] or 0
        if any(c in str(mode) for c in 'wax+') or flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):
            raise PermissionError('audit denies writes')
    if event.startswith(('subprocess.','socket.')) or event in {'os.system','os.exec','os.posix_spawn','os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime'}:
        raise PermissionError('audit denies '+event)
sys.addaudithook(audit)

def require(ok,why):
    if not ok: raise ValueError(why)
def digest(b): return hashlib.sha256(b).hexdigest()
def path(p):
    p=Path(os.path.abspath(p))
    for q in [p,*p.parents]: require(not stat.S_ISLNK(q.lstat().st_mode),'symlink ancestry')
    return p
def read(p):
    p=path(p); fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
    try:
        a=os.fstat(fd);require(stat.S_ISREG(a.st_mode) and a.st_nlink==1,'not single regular file')
        chunks=[]
        while True:
            b=os.read(fd,1048576)
            if not b:break
            chunks.append(b)
        z=os.fstat(fd);require((a.st_dev,a.st_ino,a.st_size,a.st_mtime_ns)==(z.st_dev,z.st_ino,z.st_size,z.st_mtime_ns),'file changed')
        return b''.join(chunks)
    finally:os.close(fd)
def pairs(items):
    d={}
    for k,v in items:
        require(k not in d,'duplicate JSON key');d[k]=v
    return d
def parse(b): return json.loads(b,object_pairs_hook=pairs)
def rel(s,root=False):
    require(isinstance(s,str),'nonstring path')
    if root and s=='':return
    require(s and not s.startswith('/') and '\\' not in s and '\x00' not in s and all(x not in ('','.','..') for x in s.split('/')),'unsafe relative path')
def inventory(root):
    fs={};ds={}
    for base,dirs,files in os.walk(root,followlinks=False):
        base=Path(base);q=base.lstat();require(stat.S_ISDIR(q.st_mode),'not directory')
        ds[str(base.relative_to(root)) if base!=root else '']=stat.S_IMODE(q.st_mode)
        for name in dirs:
            q=(base/name).lstat();require(stat.S_ISDIR(q.st_mode),'non-directory child')
        for name in files:
            p=base/name;q=p.lstat();require(stat.S_ISREG(q.st_mode) and q.st_nlink==1,'nonregular/hardlinked payload')
            s=str(p.relative_to(root));rel(s)
            if s=='MANIFEST.json':continue
            b=read(p);fs[s]={'bytes':len(b),'sha256':digest(b),'mode':stat.S_IMODE(q.st_mode)}
    return dict(sorted(fs.items())),dict(sorted(ds.items()))
def run():
    ap=argparse.ArgumentParser();ap.add_argument('--packet',required=True);ap.add_argument('--final',required=True);ap.add_argument('--final-sha256',required=True);ap.add_argument('--tree',required=True);ap.add_argument('--audit-probe',choices=['write','process'])
    a=ap.parse_args()
    if a.audit_probe=='write':
        with open(Path(a.packet)/'audit-must-not-exist','w') as f:f.write('forbidden')
        raise ValueError('audit failed')
    if a.audit_probe=='process':
        os.system('true');raise ValueError('audit failed')
    require(len(a.final_sha256)==64 and all(c in '0123456789abcdef' for c in a.final_sha256),'bad detached hash')
    root=path(a.packet);fb=read(a.final);require(digest(fb)==a.final_sha256,'detached FINAL mismatch');f=parse(fb)
    require(f['schema']=='r126-final-v1' and f['status']=='PREFREEZE_NO_NOMINEE','wrong archive status')
    mb=read(root/'MANIFEST.json');require(digest(mb)==f['manifest_sha256'],'manifest mismatch');m=parse(mb)
    require(set(m)=={'schema','files','directories'} and m['schema']=='r126-exact-manifest-v1','manifest schema')
    require(list(m['files'])==sorted(m['files']) and list(m['directories'])==sorted(m['directories']),'unsorted inventory')
    for s in m['files']:rel(s)
    for s in m['directories']:rel(s,True)
    fs,ds=inventory(root);require(fs==m['files'] and ds==m['directories'],'exact inventory mismatch')
    require(digest(read(root/'public/report.md'))==f['report_sha256'],'report binding')
    require(digest(read(root/'public/verify.py'))==f['verifier_sha256'],'verifier binding')
    require(digest(read(Path(__file__)))==f['verifier_sha256'],'running verifier binding')
    ids=parse(read(root/'private/project-input-identities.json'));require(ids['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin')
    tb=read(a.tree);td=next(x for x in ids['inputs'] if x['path']=='sources/preprints-tree.json');require(digest(tb)==td['sha256'],'canonical tree anchor')
    t=parse(tb);require(t['truncated'] is False and len(t['tree'])==13223,'complete tree required')
    by={x['path']:x for x in t['tree']};require(len(by)==13223,'duplicate canonical paths')
    nr=0
    for register in ['canonical.json','canonical236.json']:
        for r in parse(read(root/'private'/register)):
            c=r['canonical'];require(by.get(c['path'])==c,'full canonical record mismatch');rel(r['local'])
            b=read(root/r['local']);require(len(b)==c['size'] and digest(b)==r['sha256'],'source bytes')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'],'source git blob')
            require(r['pinned_raw_url']=='https://raw.githubusercontent.com/openai/math/'+ids['pin']+'/'+c['path'],'pinned raw URL');nr+=1
    np=nfail=0
    for name in ['receipts.json','screen-receipts.json']:
        for r in parse(read(root/'private/primary'/name)):
            if r['status']=='failure':nfail+=1;continue
            p=root/'private/primary'/r['name'];b=read(p.with_suffix('.pdf'));z=read(p.with_suffix('.txt'))
            require(digest(b)==r['pdf_sha256'] and len(b)==r['pdf_bytes'] and digest(z)==r['text_sha256'] and r['extraction_exit']==0,'primary pair');np+=1
    nh=0
    for r in parse(read(root/'private/history-register.json')):
        rel(r['local']);b=read(root/r['local']);require(digest(b)==r['sha256'] and len(b)==r['bytes'],'history copy');nh+=1
    print(json.dumps({'status':'VERIFIED_ARTIFACT_ONLY','payloads':len(fs),'directories_including_root':len(ds),'canonical_records':nr,'primary_pairs':np,'recorded_access_failures':nfail,'history_copies':nh,'mathematical_gate':False},sort_keys=True))
try:run()
except Exception as e:
    print('REJECT: '+str(e),file=sys.stderr);sys.exit(2)
