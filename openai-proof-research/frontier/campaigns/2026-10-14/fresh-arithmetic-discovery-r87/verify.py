#!/usr/bin/env python3
"""Original r87 read-only artifact verifier. MIT. Integrity only, not mathematics."""
import sys
sys.dont_write_bytecode = True
import argparse, hashlib, json, os, re, stat
from pathlib import Path
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREEHASH='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def audit(event,args):
    if event=='open':
        mode=args[1] if len(args)>1 else None
        flags=args[2] if len(args)>2 else 0
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('READ_ONLY_WRITE_DENIED')
    if event in {'os.remove','os.rmdir','os.mkdir','os.rename','os.link','os.symlink','os.chmod','os.chown','os.utime','os.truncate','os.putenv','os.unsetenv'}:
        raise RuntimeError('READ_ONLY_WRITE_DENIED')
    if event.startswith(('subprocess.','os.exec','os.spawn','os.fork','os.posix_spawn')) or event=='os.system':
        raise RuntimeError('READ_ONLY_PROCESS_DENIED')
    if event.startswith('socket.'):
        raise RuntimeError('READ_ONLY_NETWORK_DENIED')
sys.addaudithook(audit)
def require(ok,msg):
    if not ok: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def safe(s):
    require(isinstance(s,str) and s and '\\' not in s,'UNSAFE_PATH')
    p=Path(s);require(not p.is_absolute() and all(x not in {'','..','.'} for x in s.split('/')),'UNSAFE_PATH')
    return p
def reg(p):
    t=p.lstat();require(stat.S_ISREG(t.st_mode),'NONREGULAR_FILE:'+str(p));require(t.st_nlink==1,'HARDLINK:'+str(p));return t
def spec(p):
    t=reg(p);b=p.read_bytes();return dict(sha256=digest(b),bytes=len(b),mode=stat.S_IMODE(t.st_mode))
def scan(root):
    require(root.is_dir() and not root.is_symlink(),'INVALID_PACKET_ROOT')
    files={};dirs={'.':stat.S_IMODE(root.lstat().st_mode)}
    for base,dn,fn in os.walk(root,followlinks=False):
        for n in dn:
            p=Path(base)/n;t=p.lstat();require(stat.S_ISDIR(t.st_mode),'NONREGULAR_DIRECTORY:'+str(p));dirs[str(p.relative_to(root))]=stat.S_IMODE(t.st_mode)
        for n in fn:
            p=Path(base)/n;files[str(p.relative_to(root))]=spec(p)
    return files,dirs
def load(p):reg(p);return json.loads(p.read_text())
def main():
    a=argparse.ArgumentParser();a.add_argument('root',type=Path);a.add_argument('--finalhash',required=True);a.add_argument('--reporthash',required=True);a.add_argument('--tree',required=True,type=Path);a.add_argument('--probe-write',action='store_true');a.add_argument('--probe-process',action='store_true');o=a.parse_args()
    for x in [o.finalhash,o.reporthash]:require(re.fullmatch('[0-9a-f]{64}',x) is not None,'INVALID_DETACHED_ANCHOR')
    root=o.root.absolute();require(root.is_dir() and not root.is_symlink(),'INVALID_ROOT');require(Path(__file__).absolute()==root/'verify.py','OWN_VERIFIER_REQUIRED')
    reg(root/'FINAL.json');require(digest((root/'FINAL.json').read_bytes())==o.finalhash,'FINAL_ANCHOR_MISMATCH')
    final=load(root/'FINAL.json');require(final['schema']=='r87-final-v1' and final['pin']==PIN,'FINAL_SCHEMA')
    require(set(final['outside'])=={'MANIFEST.json','REPORT.md','verify.py','run_controls.py'},'OUTSIDE_BINDING_SET')
    for p,s in final['outside'].items(): require(spec(root/safe(p))==s,'OUTSIDE_BINDING_MISMATCH:'+p)
    require(final['outside']['REPORT.md']['sha256']==o.reporthash,'REPORT_ANCHOR_MISMATCH')
    require(spec(root/'packet/public/report.md')==final['packet_report'],'PACKET_REPORT_BINDING')
    manifest=load(root/'MANIFEST.json');require(manifest['schema']=='r87-manifest-v1' and manifest['pin']==PIN,'MANIFEST_SCHEMA')
    files,dirs=scan(root/'packet')
    for p in manifest['files']:safe(p)
    for p in manifest['directories']:
        if p!='.':safe(p)
    require(set(files)==set(manifest['files']),'FILE_MEMBERSHIP_MISMATCH');require(set(dirs)==set(manifest['directories']),'DIRECTORY_MEMBERSHIP_MISMATCH')
    for p,s in manifest['files'].items():require(files[p]==s,'PAYLOAD_MISMATCH:'+p)
    require(dirs==manifest['directories'],'DIRECTORY_MODE_MISMATCH')
    reg(o.tree);tb=o.tree.read_bytes();require(digest(tb)==TREEHASH==final['tree_sha256'],'TREE_ANCHOR_MISMATCH');tree=json.loads(tb)
    require(tree['truncated'] is False and len(tree['tree'])==13223,'TREE_COMPLETENESS');index={r['path']:r for r in tree['tree']};require(len(index)==13223,'TREE_DUPLICATE')
    p=root/'packet';require(digest((p/'private/context/preprints-tree.json').read_bytes())==TREEHASH,'COPIED_TREE_MISMATCH')
    up=load(p/'private/context/upstream.json');require(PIN in json.dumps(up),'UPSTREAM_PIN')
    sources=load(p/'public/source-register.json');receipts=load(p/'private/upstream/receipts.json');require(len(sources)==len(receipts)==22,'SOURCE_COUNT');require(len({r['path'] for r in sources})==22,'SOURCE_DUPLICATE')
    receiptindex={r['path']:r for r in receipts};locals_=[]
    for r in sources:
        path=r['path'];local=safe(r['local']);require(str(local)=='private/upstream/'+path,'SOURCE_LOCAL_PATH')
        require(index.get(path)==r['canonical_record'] and r['canonical_record']['type']=='blob','CANONICAL_RECORD_MISMATCH')
        require(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,'SOURCE_RAW_URL')
        require({k:r[k] for k in receiptindex[path]}==receiptindex[path],'SOURCE_RECEIPT_MISMATCH')
        b=(p/local).read_bytes();require(len(b)==r['bytes']==r['canonical_record']['size'] and digest(b)==r['sha256'],'SOURCE_BYTES')
        require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['blob']==r['canonical_record']['sha'],'SOURCE_GIT_BLOB')
        require(re.findall(r'\\label\{([^}]+)\}',b.decode())==r['labels_present_not_all_read'],'SOURCE_LABEL_INVENTORY');locals_.append(str(local))
    expected=set(locals_)|{'private/upstream/receipts.json'};require({n for n in files if n.startswith('private/upstream/')}==expected,'SOURCE_INVENTORY')
    prim=load(p/'public/primary-register.json');pr=load(p/'private/primary/receipts.json');require(len(prim)==len(pr)==5,'PRIMARY_COUNT');pi={r['name']:r for r in pr}
    for r in prim:
        require({k:r[k] for k in pi[r['name']]}==pi[r['name']],'PRIMARY_RECEIPT')
        b=(p/safe(r['pdf_local'])).read_bytes();require(digest(b)==r['sha256'] and len(b)==r['bytes'],'PRIMARY_PDF')
        require(digest((p/safe(r['text_local'])).read_bytes())==r['text_sha256'],'PRIMARY_TEXT')
    for name,n in [('history',10),('context',23)]:
        records=load(p/('public/'+name+'-register.json'));require(len(records)==n,name.upper()+'_COUNT')
        require(len({r['local'] for r in records})==n,name.upper()+'_DUPLICATE')
        for r in records:
            b=(p/safe(r['local'])).read_bytes();require(digest(b)==r['sha256'] and len(b)==r['bytes'],name.upper()+'_COPY')
    if o.probe_write:(root/'MUST_NOT_EXIST').write_text('denied')
    if o.probe_process:
        import subprocess
        subprocess.run([sys.executable,'-c','pass'],check=True)
    print(json.dumps({'status':'INTEGRITY_ONLY_VERIFIED','payload_files':len(files),'directories':len(dirs),'canonical_sources':len(sources),'primary_pairs':len(prim),'tree_entries':13223,'final_sha256':o.finalhash,'report_sha256':o.reporthash},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print(json.dumps({'status':'REJECTED','reason':str(e)},sort_keys=True));sys.exit(1)
