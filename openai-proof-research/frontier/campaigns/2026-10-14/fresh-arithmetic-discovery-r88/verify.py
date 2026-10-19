#!/usr/bin/env python3
"""Original r88 read-only artifact verifier. Integrity only; not a mathematical gate."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath
sys.dont_write_bytecode = True

def guard(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise PermissionError('DENIED_WRITE')
    if event.startswith(('socket.', 'subprocess.')) or event in {'os.system','os.posix_spawn','os.fork','os.forkpty','os.exec'}:
        raise PermissionError('DENIED_PROCESS_OR_NETWORK')
    if event in {'os.remove','os.rmdir','os.mkdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.truncate','os.utime'}:
        raise PermissionError('DENIED_MUTATION')
sys.addaudithook(guard)
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREEHASH='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def fail(msg):
    raise ValueError(msg)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def unique(pairs):
    d={}
    for k,v in pairs:
        if k in d: fail('duplicate JSON key')
        d[k]=v
    return d

def parsed(b):
    return json.loads(b,object_pairs_hook=unique)

def safe(s, root=False):
    if root and s=='.': return s
    if not isinstance(s,str) or not s or '\\' in s or '\x00' in s: fail('unsafe path')
    p=PurePosixPath(s)
    if p.is_absolute() or any(x in {'','.', '..'} for x in s.split('/')) or str(p)!=s: fail('unsafe path')
    return s

def regular(p):
    st=p.lstat()
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1: fail('not a singly linked regular file: '+str(p))
    if not stat.S_IMODE(st.st_mode)&0o444: fail('unreadable mode: '+str(p))
    return st

def data(p):
    regular(p)
    return p.read_bytes()

def authenticated(p,m):
    st=regular(p);b=p.read_bytes()
    if set(m)!={'sha256','size','mode'}: fail('file metadata schema')
    if len(b)!=m['size'] or sha(b)!=m['sha256'] or stat.S_IMODE(st.st_mode)!=m['mode']: fail('file identity: '+str(p))
    return b

def walk(p):
    files={};dirs={}
    def visit(d,rel):
        st=d.lstat()
        if not stat.S_ISDIR(st.st_mode): fail('not directory: '+str(d))
        mode=stat.S_IMODE(st.st_mode)
        if mode&0o555==0: fail('inaccessible directory mode')
        dirs[rel]=mode
        with os.scandir(d) as it:
            for e in it:
                ep=Path(e.path);s=e.name if rel=='.' else rel+'/'+e.name;safe(s)
                es=e.stat(follow_symlinks=False)
                if stat.S_ISDIR(es.st_mode):visit(ep,s)
                elif stat.S_ISREG(es.st_mode):files[s]=ep
                else:fail('special file or symlink: '+s)
    visit(p,'.');return files,dirs

def main():
    a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--finalhash',required=True);a.add_argument('--reporthash',required=True);a.add_argument('--tree');a.add_argument('--probe-write',action='store_true');a.add_argument('--probe-process',action='store_true');a=a.parse_args()
    for h in [a.finalhash,a.reporthash]:
        if not re.fullmatch('[0-9a-f]{64}',h):fail('invalid detached hash')
    rawroot=Path(a.root).absolute()
    if rawroot.is_symlink():fail('root symlink')
    r=rawroot.resolve()
    if a.probe_write:
        with open(r/'DENIED_WRITE','w') as f:f.write('must not happen')
        fail('write guard did not deny')
    if a.probe_process:
        os.system('true');fail('process guard did not deny')
    fb=data(r/'FINAL.json')
    if sha(fb)!=a.finalhash:fail('detached FINAL mismatch')
    f=parsed(fb)
    if set(f)!={'schema','pin','status','anchors'} or f['schema']!='r88-final-v1' or f['pin']!=PIN or f['status']!='PREFREEZE_NO_NOMINEE':fail('FINAL schema')
    if set(f['anchors'])!={'MANIFEST.json','REPORT.md','verify.py','run_controls.py'}:fail('anchor inventory')
    anchor={k:authenticated(r/k,v) for k,v in f['anchors'].items()}
    if sha(anchor['REPORT.md'])!=a.reporthash:fail('detached REPORT mismatch')
    if Path(__file__).resolve()!=r/'verify.py':fail('must execute selected OWN verifier')
    m=parsed(anchor['MANIFEST.json'])
    if set(m)!={'schema','pin','files','directories'} or m['schema']!='r88-packet-v1' or m['pin']!=PIN:fail('manifest schema')
    for k in m['files']:safe(k)
    for k,v in m['directories'].items():
        safe(k,True)
        if not isinstance(v,int) or v<0 or v>0o7777:fail('directory metadata')
    files,dirs=walk(r/'packet')
    if set(files)!=set(m['files']) or dirs!=m['directories']:fail('exact packet membership or directory mode mismatch')
    for k,v in m['files'].items():authenticated(files[k],v)
    packet=r/'packet'
    tb=data(packet/'private/context/preprints-tree.json')
    if sha(tb)!=TREEHASH:fail('canonical complete tree identity')
    if a.tree and data(Path(a.tree))!=tb:fail('external tree mismatch')
    tree=parsed(tb)
    if tree['truncated'] is not False or len(tree['tree'])!=13223:fail('complete tree schema')
    by={x['path']:x for x in tree['tree']}
    if len(by)!=13223:fail('duplicate canonical path')
    acq=parsed(data(packet/'private/acquisition.json'));sr=parsed(data(packet/'private/source-register.json'))
    seen=set();ret=[]
    for x in acq:
        c=x['canonical'];cp=safe(c['path']);lp=safe(x['local'])
        if cp in seen or by.get(cp)!=c or c['type']!='blob':fail('canonical record mismatch')
        seen.add(cp)
        if lp!='private/upstream/'+cp.removeprefix('preprints/'):fail('source local path')
        if x['url']!='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+cp:fail('pinned raw URL')
        if x['bytes']!=c['size']:fail('canonical size')
        if x['retained'] is True:
            b=data(packet/lp)
            if sha(b)!=x['sha256'] or len(b)!=c['size'] or hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=c['sha']:fail('source blob identity')
            if re.findall(r'\\label\{([^}]+)\}',b.decode())!=x['labels_navigation_only']:fail('source label inventory')
            ret.append(x)
        elif x['retained'] is not False or (packet/lp).exists():fail('removed acquisition state')
    if ret!=sr:fail('retained register mismatch')
    if {x['local'] for x in sr}!={x for x in files if x.startswith('private/upstream/')}:fail('source file inventory')
    prim=parsed(data(packet/'private/primary/register.json'))
    for x in prim:
        n=x['name']
        if not re.fullmatch('[A-Za-z0-9]+',n):fail('primary name')
        b=data(packet/('private/primary/'+n+'.pdf'));t=data(packet/('private/primary/'+n+'.txt'))
        if not b.startswith(b'%PDF') or sha(b)!=x['sha256'] or len(b)!=x['size'] or sha(t)!=x['text_sha256'] or x['returncode']!=0:fail('primary identity')
    hist=parsed(data(packet/'private/history-register.json'))
    for x in hist:
        safe(x['origin']);safe(x['local']);b=data(packet/x['local'])
        if sha(b)!=x['sha256'] or len(b)!=x['bytes']:fail('history identity')
    print(json.dumps(dict(status='INTEGRITY_ONLY',payload_files=len(files),directories_including_root=len(dirs),canonical_acquisitions=len(acq),retained_sources=len(sr),primary_pairs=len(prim),history_copies=len(hist),final_sha256=a.finalhash,report_sha256=a.reporthash),sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as e:
        print('REJECT: '+type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
