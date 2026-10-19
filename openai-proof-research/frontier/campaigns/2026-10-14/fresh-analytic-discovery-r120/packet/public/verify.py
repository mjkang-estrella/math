#!/usr/bin/env python3
"""Read-only detached-anchor verifier. Integrity/provenance only, never mathematics."""
import argparse,hashlib,json,os,re,stat,sys
sys.dont_write_bytecode=True
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def guard(event,args):
    if event=='open' and ((isinstance(args[1],str) and any(c in args[1] for c in 'wax+')) or (isinstance(args[2],int) and args[2] & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND))):
        raise RuntimeError('read-only verifier: write denied')
    if event.startswith(('subprocess.','socket.')) or event in {'os.remove','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.system','os.utime'}:
        raise RuntimeError('read-only verifier: mutation/process/network denied')
sys.addaudithook(guard)
def fail(s):raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def regular(p):
    st=os.lstat(p)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:fail('nonregular or multiply linked file: '+str(p))
    return st

def read(p):regular(p);return open(p,'rb').read()
def safe_rel(p):
    if not isinstance(p,str) or not p or p.startswith('/') or any(x in ('','..','.') for x in p.split('/')):fail('unsafe relative path')
def directory(p):
    s=os.lstat(p)
    if not stat.S_ISDIR(s.st_mode):fail('non-directory/symlink: '+str(p))
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for x in ['root','tree','finalhash','reporthash']:ap.add_argument('--'+x,required=True)
    a=ap.parse_args()
    for h in [a.finalhash,a.reporthash]:
        if not re.fullmatch('[0-9a-f]{64}',h):fail('invalid detached hash')
    root=os.path.abspath(a.root)
    p=root
    while True:
        directory(p)
        q=os.path.dirname(p)
        if q==p:break
        p=q
    final=read(root+'/FINAL.json')
    if sha(final)!=a.finalhash:fail('detached FINAL mismatch')
    f=json.loads(final)
    if f['schema']!='r120-final-v1' or f['pin']!=PIN or f['status']!='PREFREEZE' or f['frozen_target'] is not None:fail('final contract')
    man=read(root+'/MANIFEST.json')
    if sha(man)!=f['manifest_sha256']:fail('manifest mismatch')
    m=json.loads(man)
    if m['schema']!='r120-manifest-v1' or m['scope']!='packet':fail('manifest contract')
    pkt=root+'/packet';directory(pkt)
    if stat.S_IMODE(os.lstat(pkt).st_mode)!=m['packet_mode']:fail('packet mode')
    actual={}
    for base,dirs,files in os.walk(pkt,followlinks=False):
        for n in dirs:
            p=base+'/'+n;directory(p);actual[os.path.relpath(p,pkt)]={'type':'directory','mode':stat.S_IMODE(os.lstat(p).st_mode)}
        for n in files:
            p=base+'/'+n;s=regular(p);b=read(p);actual[os.path.relpath(p,pkt)]={'type':'file','mode':stat.S_IMODE(s.st_mode),'bytes':len(b),'sha256':sha(b)}
    if actual!=m['entries']:fail('exact packet inventory/mode/hash mismatch')
    for rel in m['entries']:safe_rel(rel)
    report=read(pkt+'/public/report.md')
    if sha(report)!=a.reporthash or sha(report)!=f['report_sha256']:fail('detached report mismatch')
    tb=read(a.tree)
    if sha(tb)!=TREE or f['tree_sha256']!=TREE:fail('complete-tree hash mismatch')
    t=json.loads(tb)
    if t['truncated'] is not False or len(t['tree'])!=13223:fail('complete-tree structure')
    by={e['path']:e for e in t['tree']}
    if len(by)!=13223:fail('duplicate tree paths')
    sr=json.loads(read(pkt+'/public/source-register.json'))
    for e in sr:
        safe_rel(e['local']);b=read(pkt+'/'+e['local']);z=by[e['path']]
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        if z['type']!='blob' or blob!=z['sha'] or blob!=e['git_blob'] or sha(b)!=e['sha256'] or len(b)!=e['bytes']:fail('source identity')
        if e['url']!='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'] or e['retained'] is not True:fail('source URL/retention')
    pr=json.loads(read(pkt+'/public/primary-register.json'))
    for e in pr:
        if e['status']!='success':fail('primary status')
        for k in ['pdf','text']:
            safe_rel(e[k])
            if sha(read(pkt+'/'+e[k]))!=e[k+'_sha256']:fail('primary identity')
    hr=json.loads(read(pkt+'/public/history-register.json'))
    for e in hr:
        safe_rel(e['local']);b=read(pkt+'/'+e['local'])
        if sha(b)!=e['sha256'] or len(b)!=e['bytes']:fail('history copy identity')
    c=json.loads(read(pkt+'/public/context.json'))
    if c['pin']!=PIN or c['tree_sha256']!=TREE or c['truncated'] is not False or c['entries']!=13223 or c['frozen_target'] is not None:fail('context contract')
    print(json.dumps({'integrity':'matched','files':sum(e['type']=='file' for e in actual.values()),'directories':sum(e['type']=='directory' for e in actual.values()),'canonical_sources':len(sr),'primary_pairs':len(pr),'history_copies':len(hr),'mathematical_gate':False},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
