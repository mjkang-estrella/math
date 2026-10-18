#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Disposable ZIP and extraction controls, using external integrity anchors."""
import argparse,json,os,shutil,subprocess,sys,tempfile,zipfile
from pathlib import Path
sys.dont_write_bytecode=True
p=argparse.ArgumentParser();p.add_argument('bundle',type=Path);p.add_argument('--manifest-sha256',required=True);p.add_argument('--gate-sha256',required=True);a=p.parse_args()
here=Path(__file__).resolve().parent;tmp=Path(tempfile.mkdtemp(prefix='t117q-bundle-controls-',dir='/var/tmp'));results=[]
def check(label,path,positive=False,m=None,g=None):
    r=subprocess.run([sys.executable,'-B',str(here/'verify_bundle.py'),str(path),'--manifest-sha256',m or a.manifest_sha256,'--gate-sha256',g or a.gate_sha256],capture_output=True,text=True)
    ok=(r.returncode==0)==positive
    if not ok:raise RuntimeError(label+': '+r.stdout+r.stderr)
    results.append(dict(name=label,pass_=ok,returncode=r.returncode))
check('positive ZIP',a.bundle,True)
check('wrong external manifest',a.bundle,m='0'*64);check('wrong external gate',a.bundle,g='0'*64)
base=tmp/'base'
with zipfile.ZipFile(a.bundle) as z:z.extractall(base)
check('positive extraction',base,True)
for kind in ['changed','missing','extra-file','extra-dir','symlink','hardlink','fifo']:
    d=tmp/kind;shutil.copytree(base,d);f=d/'README.md'
    if kind=='changed':f.write_bytes(f.read_bytes()+b'x')
    elif kind=='missing':f.unlink()
    elif kind=='extra-file':(d/'extra').write_text('x')
    elif kind=='extra-dir':(d/'empty').mkdir()
    elif kind=='symlink':f.unlink();f.symlink_to(base/'README.md')
    elif kind=='hardlink':f.unlink();os.link(base/'README.md',f)
    elif kind=='fifo':f.unlink();os.mkfifo(f)
    check(kind,d)
    if kind=='hardlink':f.unlink()
for kind in ['duplicate','traversal','zip-symlink']:
    dest=tmp/(kind+'.zip');shutil.copyfile(a.bundle,dest)
    with zipfile.ZipFile(dest,'a') as z:
        name='README.md' if kind=='duplicate' else '../escape' if kind=='traversal' else 'link'
        i=zipfile.ZipInfo(name);i.external_attr=(0o120777 if kind=='zip-symlink' else 0o100644)<<16;z.writestr(i,b'x')
    check(kind,dest)
check('restored baseline',base,True)
print(json.dumps(dict(status='PASS',controls=len(results),temporary_directory=str(tmp),results=results),indent=2))
