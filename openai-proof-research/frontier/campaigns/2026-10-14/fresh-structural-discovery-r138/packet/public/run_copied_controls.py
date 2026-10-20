#!/usr/bin/env python3
"""Disposable integrity controls, writing only under the supplied r138 root/work.
Run with python -B and the same detached anchors as verify.py. No math verdict.
"""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True,type=Path);ap.add_argument('--project',required=True,type=Path)
    for s in ['final','manifest','report']:ap.add_argument('--'+s+'-sha256',required=True)
    a=ap.parse_args();root=a.root.resolve();work=root/'work';work.mkdir(exist_ok=True)
    tmp=Path(tempfile.mkdtemp(prefix='copied-controls-',dir=work));receipts=[]
    for case in ['baseline','payload','extra','report','symlink','forged-reseal']:
        dest=tmp/case;dest.mkdir()
        shutil.copytree(root/'packet',dest/'packet')
        for n in ['FINAL.json','REPORT.md']:shutil.copy2(root/n,dest/n)
        target=dest/'packet/public/derivations.md'
        if case=='payload':target.write_bytes(target.read_bytes()+b'\nchanged\n')
        if case=='extra':(dest/'packet/private/unlisted').write_text('extra\n')
        if case=='report':(dest/'REPORT.md').write_bytes((dest/'REPORT.md').read_bytes()+b'\nchanged\n')
        if case=='symlink':target.unlink();target.symlink_to(root/'packet/public/derivations.md')
        if case=='forged-reseal':
            target.write_bytes(target.read_bytes()+b'\nforged\n')
            mpath=dest/'packet/MANIFEST.json';m=json.loads(mpath.read_text());b=target.read_bytes()
            m['files']['public/derivations.md'].update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
            mpath.write_text(json.dumps(m,indent=2)+'\n')
            fpath=dest/'FINAL.json';f=json.loads(fpath.read_text());f['manifest_sha256']=hashlib.sha256(mpath.read_bytes()).hexdigest();fpath.write_text(json.dumps(f,indent=2)+'\n')
        cmd=[sys.executable,'-B',str(root/'packet/public/verify.py'),'--root',str(dest),'--project',str(a.project)]
        for n in ['final','manifest','report']:cmd+=['--'+n+'-sha256',getattr(a,n+'_sha256')]
        env=os.environ.copy();env['TMPDIR']=str(tmp);env['PYTHONDONTWRITEBYTECODE']='1'
        z=subprocess.run(cmd,capture_output=True,text=True,env=env)
        ok=(z.returncode==0) if case=='baseline' else (z.returncode!=0)
        receipts.append(dict(case=case,expected_behavior=ok,returncode=z.returncode,stdout=z.stdout,stderr=z.stderr))
    out=work/'copied-controls-receipt.json';out.write_text(json.dumps(receipts,indent=2)+'\n')
    assert all(e['expected_behavior'] for e in receipts)
    print(json.dumps(dict(cases=len(receipts),all_expected=True,receipt=str(out))))
if __name__=='__main__':main()
