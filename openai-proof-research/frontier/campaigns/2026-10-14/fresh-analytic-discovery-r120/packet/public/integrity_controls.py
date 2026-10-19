#!/usr/bin/env python3
"""Run final integrity controls on disposable COPIES; never a mathematical gate."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
def sha(b):return hashlib.sha256(b).hexdigest()
def snap(r):
    out={}
    for p in sorted(r.rglob('*')):
        if p.relative_to(r).parts[0]=='controls':continue
        st=p.lstat();out[str(p.relative_to(r))]=[stat.S_IMODE(st.st_mode),st.st_nlink,sha(p.read_bytes()) if p.is_file() else 'directory']
    return out
ap=argparse.ArgumentParser()
for k in ['root','tree','finalhash','reporthash']:ap.add_argument('--'+k,required=True)
a=ap.parse_args();r=Path(a.root).resolve();base=r/'controls';base.mkdir(exist_ok=True)
before=snap(r);original_verifier=r/'packet/public/verify.py'
results=[]
cases=['valid','missing-finalhash','missing-reporthash','wrong-finalhash','wrong-reporthash','changed-report','changed-source','changed-primary','changed-history','changed-verifier','extra-file','extra-directory','missing-file','changed-mode','symlink','hardlink','changed-manifest','changed-final','coherent-reseal','wrong-tree']
for case in cases:
    c=base/('copy-'+case)
    if c.exists():raise RuntimeError('existing control copy')
    c.mkdir();shutil.copytree(r/'packet',c/'packet')
    for f in ['MANIFEST.json','FINAL.json']:shutil.copy2(r/f,c/f)
    report=c/'packet/public/report.md';tree=Path(a.tree)
    if case=='changed-report':report.write_bytes(report.read_bytes()+b'changed\n')
    if case=='changed-source':
        q=next((c/'packet/private/upstream').rglob('*.tex'));q.write_bytes(q.read_bytes()+b'changed\n')
    if case=='changed-primary':q=c/'packet/private/primary/goww.txt';q.write_bytes(q.read_bytes()+b'changed\n')
    if case=='changed-history':q=next((c/'packet/private/history').glob('*'));q.write_bytes(q.read_bytes()+b'changed\n')
    if case=='changed-verifier':q=c/'packet/public/verify.py';q.write_bytes(q.read_bytes()+b'# changed\n')
    if case=='extra-file':(c/'packet/extra').write_text('extra')
    if case=='extra-directory':(c/'packet/empty-extra').mkdir()
    if case=='missing-file':(c/'packet/public/RIGHTS.md').unlink()
    if case=='changed-mode':report.chmod(0o600 if stat.S_IMODE(report.stat().st_mode)!=0o600 else 0o644)
    if case=='symlink':report.unlink();report.symlink_to(r/'packet/public/report.md')
    if case=='hardlink':q=c/'duplicate';os.link(report,q)
    if case=='changed-manifest':q=c/'MANIFEST.json';q.write_bytes(q.read_bytes()+b' ')
    if case=='changed-final':q=c/'FINAL.json';q.write_bytes(q.read_bytes()+b' ')
    if case=='coherent-reseal':
        report.write_bytes(report.read_bytes()+b'coherently changed\n');mp=c/'MANIFEST.json';m=json.loads(mp.read_text());e=m['entries']['public/report.md'];e['bytes']=report.stat().st_size;e['sha256']=sha(report.read_bytes());mp.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');fp=c/'FINAL.json';f=json.loads(fp.read_text());f['manifest_sha256']=sha(mp.read_bytes());f['report_sha256']=sha(report.read_bytes());fp.write_text(json.dumps(f,indent=2,sort_keys=True)+'\n')
    if case=='wrong-tree':tree=c/'wrong-tree.json';tree.write_text('{"tree":[],"truncated":false}')
    cmd=[sys.executable,'-B',str(original_verifier),'--root',str(c),'--tree',str(tree)]
    if case!='missing-finalhash':cmd+=['--finalhash','0'*64 if case=='wrong-finalhash' else a.finalhash]
    if case!='missing-reporthash':cmd+=['--reporthash','0'*64 if case=='wrong-reporthash' else a.reporthash]
    copy_before=snap(c);p=subprocess.run(cmd,capture_output=True,text=True);copy_after=snap(c)
    # For the symlink case snap follows only this copied file to read its unchanged target.
    ok=(p.returncode==0)==(case=='valid') and copy_before==copy_after
    results.append({'case':case,'expected':'accept' if case=='valid' else 'reject','returncode':p.returncode,'matched_expectation':ok,'copy_unchanged_by_verifier':copy_before==copy_after,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()})
    shutil.rmtree(c)
    if not ok:raise RuntimeError('failed control '+case)
after=snap(r)
if before!=after:raise RuntimeError('original owned root changed')
receipt={'finalhash':a.finalhash,'reporthash':a.reporthash,'controls':results,'original_owned_root_excluding_controls_unchanged':True,'original_snapshot_sha256':sha(json.dumps(before,sort_keys=True).encode()),'mathematical_gate':False}
(base/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'controls':len(results),'all_expected':True,'original_unchanged':True,'receipt_sha256':sha((base/'receipt.json').read_bytes()),'mathematical_gate':False}))
