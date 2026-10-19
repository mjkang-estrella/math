#!/usr/bin/env python3
"""Read-only artifact verifier. Not a mathematical or contribution gate."""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_HASH = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def guard(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (isinstance(flags, int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('verifier denies write open')
    if event in {'os.remove','os.rename','os.rmdir','os.mkdir','os.link','os.symlink','os.chmod','os.chown','os.truncate','os.utime','os.system','subprocess.Popen'} or event.startswith('socket.'):
        raise PermissionError('verifier denies mutation/network/process: '+event)
sys.addaudithook(guard)

def require(ok, message):
    if not ok: raise ValueError(message)
def digest(b): return hashlib.sha256(b).hexdigest()
def read(p):
    st=p.lstat();require(stat.S_ISREG(st.st_mode),'not regular: '+str(p));require(st.st_nlink==1,'hard link: '+str(p));return p.read_bytes()
def rel(s):
    p=Path(s);require(not p.is_absolute() and p.as_posix()==s and all(x not in ('','..','.') for x in p.parts),'unsafe path');return p

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root',type=Path)
    ap.add_argument('--finalhash',required=True)
    ap.add_argument('--reporthash',required=True)
    ap.add_argument('--tree',required=True,type=Path)
    a=ap.parse_args();root=a.root.absolute()
    require(not root.is_symlink() and root.is_dir(),'unsafe root')
    fb=read(root/'FINAL.json');require(digest(fb)==a.finalhash,'detached FINAL mismatch');f=json.loads(fb)
    require(f['pin']==PIN and f['status']=='PREFREEZE_NO_NOMINEE' and f['frozen'] is False and f['nominee'] is None and f['count_assignment'] is None and f['gate_assignment'] is None,'status/pin mismatch')
    mb=read(root/'MANIFEST.json');require(digest(mb)==f['manifest_sha256'],'manifest anchor mismatch');m=json.loads(mb)
    require(m['pin']==PIN and m['format']=='r121-exact-packet-v1','manifest format')
    packet=root/'packet';require(packet.is_dir() and not packet.is_symlink(),'unsafe packet')
    actual_files={};actual_dirs=[]
    for p in sorted(packet.rglob('*')):
        s=p.relative_to(packet).as_posix();st=p.lstat()
        if stat.S_ISDIR(st.st_mode):actual_dirs.append(s)
        else:
            b=read(p);actual_files[s]={'sha256':digest(b),'bytes':len(b)}
    expected=m['files'];require(isinstance(expected,dict),'file map')
    for s in expected:rel(s)
    for s in m['directories']:rel(s)
    require(actual_files==expected,'exact file membership/hash/size mismatch')
    require(actual_dirs==m['directories'],'exact directory membership mismatch')
    rb=read(packet/'public/report.md');require(digest(rb)==a.reporthash==f['report_sha256'],'detached report mismatch')
    tb=read(a.tree);require(digest(tb)==TREE_HASH,'canonical tree hash mismatch');t=json.loads(tb)
    require(t['truncated'] is False and len(t['tree'])==13223,'complete tree contract')
    mapping={x['path']:x for x in t['tree']};require(len(mapping)==13223,'duplicate tree paths')
    sources=json.loads(read(packet/'public/source-register.json'));seen=set()
    for x in sources:
        require(x['path'] not in seen,'duplicate source');seen.add(x['path'])
        require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'],'raw URL mismatch')
        b=read(packet/rel(x['local']));entry=mapping[x['path']]
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(entry['type']=='blob' and entry['sha']==x['blob']==git,'canonical Git blob mismatch')
        require(digest(b)==x['sha256'] and len(b)==x['bytes'],'source receipt mismatch')
    for x in json.loads(read(packet/'public/acquisition-removed.json')):
        require(not (packet/rel(x['local'])).exists(),'removed acquisition present')
        require(mapping[x['path']]['sha']==x['blob'],'removed metadata blob mismatch')
        require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'],'removed URL mismatch')
    primaries=json.loads(read(packet/'public/primary-register.json'))
    for x in primaries:
        require(x['status']=='success' and x['url'].startswith('https://'),'primary status')
        for field in ['pdf','text']:require(digest(read(packet/rel(x[field])))==x[field+'_sha256'],'primary binding')
    for register in ['history-register.json','render-register.json']:
        for x in json.loads(read(packet/'public'/register)):
            require(digest(read(packet/rel(x['local'])))==x['sha256'],'history/render binding')
    print(json.dumps({'artifact_integrity':'verified','mathematical_gate':False,'files':len(actual_files),'directories':len(actual_dirs),'canonical_sources':len(sources),'primary_pairs':len(primaries),'final_sha256':a.finalhash,'report_sha256':a.reporthash},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('VERIFY_FAILED: '+str(e),file=sys.stderr);sys.exit(1)
