#!/usr/bin/env python3
"""Original r124 read-only integrity verifier. No mathematical gate."""
import sys
sys.dont_write_bytecode = True
import argparse, hashlib, json, os, re, stat
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def guard(event,args):
    if event=='open':
        mode=args[1] if len(args)>1 else None
        flags=args[2] if len(args)>2 else 0
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('DENIED write by read-only audit guard')
    if event.startswith(('subprocess.','socket.','ctypes.')) or event in {'os.system','os.exec','os.posix_spawn','os.fork','os.forkpty','os.remove','os.rename','os.rmdir','os.mkdir','os.link','os.symlink','os.chmod','os.chown','os.truncate','os.utime','shutil.copyfile','shutil.rmtree'}:
        raise PermissionError('DENIED mutation/process/network by read-only audit guard: '+event)

def require(ok,msg):
    if not ok: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def obj(pairs):
    d={}
    for k,v in pairs:
        require(k not in d,'duplicate JSON key');d[k]=v
    return d
def js(b):return json.loads(b,object_pairs_hook=obj)
def keys(x,w):require(isinstance(x,dict) and set(x)==set(w),'schema keys mismatch')
def safe(s):
    require(isinstance(s,str) and s and '\\' not in s and '\x00' not in s,'unsafe path')
    p=PurePosixPath(s)
    require(not p.is_absolute() and str(p)==s and all(v not in {'.','..',''} for v in s.split('/')),'unsafe path')
    return s

def reg(p):
    t=p.lstat();require(stat.S_ISREG(t.st_mode),'not regular file: '+str(p));require(t.st_nlink==1,'hardlink rejected: '+str(p));return t

def read(p):reg(p);return p.read_bytes()
def no_links(p):
    for q in [p,*p.parents]:require(not q.is_symlink(),'root/ancestor symlink rejected')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True)
    ap.add_argument('--probe',choices=['write','process'])
    a=ap.parse_args()
    sys.addaudithook(guard)
    if a.probe=='write':
        with open(Path(a.root)/'DENIED-PROBE','w') as f:f.write('forbidden')
    if a.probe=='process':
        import subprocess
        subprocess.run([sys.executable,'-c','pass'],check=True)
    require(re.fullmatch('[0-9a-f]{64}',a.finalhash) and re.fullmatch('[0-9a-f]{64}',a.reporthash),'detached hashes must be lowercase SHA256')
    root=Path(a.root).absolute();no_links(root);require(root.is_dir(),'root not directory')
    raw=read(root/'FINAL.json');require(digest(raw)==a.finalhash,'detached FINAL mismatch');f=js(raw)
    keys(f,['schema','pin','stage','manifest_sha256','report_sha256','public_report_sha256','verifier_sha256','controls_sha256','tree_sha256'])
    require(f['schema']=='r124-final-v1' and f['stage']=='PREFREEZE_NO_TARGET_NO_NOMINEE' and f['pin']==PIN,'final scope/schema mismatch')
    require(f['tree_sha256']==TREE,'canonical tree anchor mismatch')
    require(digest(read(root/'REPORT.md'))==a.reporthash==f['report_sha256'],'detached REPORT mismatch')
    vb=read(root/'verify.py');require(digest(vb)==f['verifier_sha256'],'verifier binding mismatch')
    require(digest(read(Path(__file__).absolute()))==f['verifier_sha256'],'executing verifier mismatch')
    require(digest(read(root/'run_controls.py'))==f['controls_sha256'],'control program binding mismatch')
    packet=root/'packet';require(stat.S_ISDIR(packet.lstat().st_mode),'packet not real directory')
    mb=read(packet/'MANIFEST.json');require(digest(mb)==f['manifest_sha256'],'manifest binding mismatch');m=js(mb)
    keys(m,['schema','files','directories']);require(m['schema']=='r124-packet-v1','manifest schema')
    require(isinstance(m['files'],list) and isinstance(m['directories'],list),'inventory type')
    expected={}
    for x in m['files']:
        keys(x,['path','size','sha256','mode']);s=safe(x['path']);require(s!='MANIFEST.json' and s not in expected,'duplicate/reserved file');expected[s]=x
        require(type(x['size']) is int and x['size']>=0 and type(x['mode']) is int,'file metadata type')
        require(re.fullmatch('[0-9a-f]{64}',x['sha256']) is not None,'file SHA type')
    dirs={}
    for x in m['directories']:
        keys(x,['path','mode']);s=safe(x['path']);require(s not in dirs and type(x['mode']) is int,'duplicate/invalid directory');dirs[s]=x['mode']
    actual_files=set();actual_dirs={}
    for base,ds,fs in os.walk(packet,followlinks=False):
        for n in ds:
            q=Path(base)/n;t=q.lstat();require(stat.S_ISDIR(t.st_mode),'special/symlink directory');actual_dirs[q.relative_to(packet).as_posix()]=stat.S_IMODE(t.st_mode)
        for n in fs:
            q=Path(base)/n;reg(q);actual_files.add(q.relative_to(packet).as_posix())
    require(actual_files==set(expected)|{'MANIFEST.json'},'exact file membership mismatch')
    require(actual_dirs==dirs,'exact directory membership/mode mismatch')
    for s,x in expected.items():
        q=packet/s;t=reg(q);require(t.st_size==x['size'] and stat.S_IMODE(t.st_mode)==x['mode'] and digest(read(q))==x['sha256'],'payload identity mismatch: '+s)
    def payload(s):
        safe(s);require(s in expected,'receipt path not in payload');return read(packet/s)
    require(digest(payload('public/report.md'))==f['public_report_sha256'],'public report binding mismatch')
    tb=payload('private/context/sources/preprints-tree.json');require(digest(tb)==TREE,'complete tree bytes mismatch');tree=js(tb)
    require(tree.get('truncated') is False and len(tree['tree'])==13223,'complete tree count/truncation mismatch')
    entries={}
    for x in tree['tree']:
        s=safe(x['path']);require(s not in entries,'duplicate canonical path');entries[s]=x
    upstream=js(payload('private/context/sources/upstream.json'));require(upstream['commit']==PIN and upstream['repository']=='https://github.com/openai/math','upstream pin mismatch')
    cb=payload('private/canonical.json');require(cb==payload('public/source-register.json'),'source register copies differ');c=js(cb)
    require(len(c)==61 and sum(x['retained'] is True for x in c)==18,'canonical acquisition counts mismatch')
    seen=set()
    for x in c:
        r=x['record'];s=safe(r['path']);require(s not in seen,'duplicate selected record');seen.add(s)
        require(entries.get(s)==r and r['type']=='blob','FULL canonical record mismatch')
        require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+s,'pinned raw URL mismatch')
        require(type(x['retained']) is bool and re.fullmatch('[0-9a-f]{64}',x['sha256']) is not None,'source receipt metadata')
        local=safe(x['local']);require(local=='private/upstream/'+x['family']+'/'+s,'canonical local path mismatch')
        if x['retained']:
            b=payload(local);require(len(b)==r['size'] and digest(b)==x['sha256'],'canonical source SHA/size mismatch')
            require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['sha'],'Git blob mismatch')
            require(re.findall(r'\\label\{([^}]+)\}',b.decode())==x['labels_present_navigation_only'],'source label inventory mismatch')
        else: require(not (packet/local).exists(),'removed source unexpectedly present')
    pb=payload('private/primary/acquisition.json');require(pb==payload('public/primary-register.json'),'primary register copies differ');prim=js(pb)
    require(sum(x.get('retained') is True and 'pdf' in x for x in prim)==5,'primary pair count mismatch')
    for x in prim:
        if x.get('retained'):
            if 'pdf' in x:
                require(x['url'].startswith('https://arxiv.org/pdf/') and re.search(r'v[1-9][0-9]*$',x['url']),'primary version URL')
                require(digest(payload(x['pdf']))==x['sha256'] and digest(payload(x['text']))==x['text_sha256'],'primary artifact mismatch')
            else:
                require(digest(payload(x['artifact']))==x['sha256'],'render artifact mismatch');payload(x['source'])
        elif x.get('ok'):
            require(not (packet/safe(x['pdf'])).exists() and not (packet/safe(x['text'])).exists(),'removed primary unexpectedly present')
    h=js(payload('public/history-register.json'));require(len(h)==16,'history count mismatch')
    for x in h:
        safe(x['origin']);b=payload(x['local']);require(len(b)==x['size'] and digest(b)==x['sha256'],'history copy mismatch')
    for x in js(payload('private/final-search-register.json')):
        b=payload('private/'+safe(x['paths']));require(digest(b)==x['sha256'] and len(b.splitlines())==x['matches'],'search receipt mismatch')
    print(json.dumps({'integrity':'verified','mathematical_gate':False,'stage':f['stage'],'files':len(expected),'subdirectories':len(dirs),'canonical_acquired':61,'canonical_retained':18,'primary_pairs':5,'history_copies':16,'final_sha256':a.finalhash,'report_sha256':a.reporthash},sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as e:
        print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
