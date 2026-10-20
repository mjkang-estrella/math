#!/usr/bin/env python3
"""Copied artifact controls. All writes are confined to supplied root/work.

Invoke with the same external anchors as verify.py. This is NOT a mathematical
gate or a syscall sandbox audit. Existing control directories are not removed.
"""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def digest_tree(root):
    out={}
    for base,dirs,files in os.walk(root):
        for name in dirs:out[str(Path(base,name).relative_to(root))]={'directory':True}
        for name in files:
            p=Path(base,name);out[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
    return out

ap=argparse.ArgumentParser();ap.add_argument('root')
for k in ['final','manifest','report']:ap.add_argument('--'+k+'-sha256',required=True)
a=ap.parse_args();root=Path(a.root).resolve();work=root/'work';work.mkdir(exist_ok=True)
copy=Path(tempfile.mkdtemp(prefix='copied-controls-',dir=work))
shutil.copytree(root/'packet',copy/'packet');shutil.copy2(root/'REPORT.md',copy/'REPORT.md')
original={'packet':digest_tree(root/'packet'),'report':hashlib.sha256((root/'REPORT.md').read_bytes()).hexdigest()}
args=[]
for k in ['final','manifest','report']:args+=['--'+k+'-sha256',getattr(a,k+'_sha256')]
results=[]
def check(name,want):
    before=digest_tree(copy)
    q=subprocess.run([sys.executable,'-B',str(copy/'packet/public/verify.py'),str(copy),*args],capture_output=True,text=True)
    unchanged=before==digest_tree(copy)
    results.append({'case':name,'expected_success':want,'returncode':q.returncode,'read_only_observed':unchanged,'output':q.stdout.strip()})
    if (q.returncode==0)!=want or not unchanged:raise RuntimeError(name+' failed')

check('intact',True)
for name,rel in [('payload','packet/public/DERIVATION.md'),('final','packet/FINAL.json'),('outside_report','REPORT.md')]:
    p=copy/rel;b=p.read_bytes();p.write_bytes(b+b'\n');check(name,False);p.write_bytes(b)
p=copy/'packet/public/unlisted.txt';p.write_text('extra');check('extra_file',False);p.unlink()
p=copy/'packet/extra-directory';p.mkdir();check('extra_directory',False);p.rmdir()
p=copy/'packet/public/DERIVATION.md';b=p.read_bytes();m=copy/'packet/MANIFEST.json';mb=m.read_bytes()
p.write_bytes(b+b'\n');data=json.loads(mb);data['files']['public/DERIVATION.md']={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()};m.write_text(json.dumps(data,indent=2)+'\n');check('forged_local_reseal_old_external_anchor',False);p.write_bytes(b);m.write_bytes(mb)
preserved=original=={'packet':digest_tree(root/'packet'),'report':hashlib.sha256((root/'REPORT.md').read_bytes()).hexdigest()}
if not preserved:raise RuntimeError('sealed originals changed')
print(json.dumps({'controls':results,'sealed_packet_and_report_unchanged':preserved,'copied_root':str(copy),'limits':'Before/after exact tree hashes, not syscall auditing. Artifact integrity only; no mathematical verdict.'},indent=2))
