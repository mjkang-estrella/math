#!/usr/bin/env python3
"""Copy-only integrity controls. Writes only below the supplied r137 root/work.
The verifier remains read-only; these checks do not review mathematics.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--project',type=Path,required=True)
    for s in ('final','manifest','report'):ap.add_argument('--'+s+'-sha256',required=True)
    a=ap.parse_args();r=a.root.resolve()
    assert r.name=='fresh-structural-discovery-r137'
    work=r/'work';work.mkdir(exist_ok=True)
    base=Path(tempfile.mkdtemp(prefix='copied-controls-',dir=work));results=[]
    cases=('baseline','payload','extra','final','manifest','report','symlink','forged-reseal')
    for case in cases:
        d=base/case;d.mkdir()
        shutil.copytree(r/'packet',d/'packet')
        for n in ('FINAL.json','REPORT.md'):shutil.copyfile(r/n,d/n)
        target=d/'packet/public/derivations.md'
        if case in ('payload','forged-reseal'):target.write_bytes(target.read_bytes()+b'\nCONTROL MUTATION\n')
        if case=='extra':(d/'packet/extra.txt').write_text('control\n')
        if case in ('final','manifest','report'):
            t=d/({'final':'FINAL.json','manifest':'packet/MANIFEST.json','report':'REPORT.md'}[case]);t.write_bytes(t.read_bytes()+b'\n')
        if case=='symlink':target.unlink();target.symlink_to(r/'packet/public/derivations.md')
        if case=='forged-reseal':
            sha=lambda b:hashlib.sha256(b).hexdigest()
            mpath=d/'packet/MANIFEST.json';m=json.loads(mpath.read_text());m['files']['public/derivations.md']['sha256']=sha(target.read_bytes());m['files']['public/derivations.md']['bytes']=target.stat().st_size;mpath.write_text(json.dumps(m,indent=2)+'\n')
            fpath=d/'FINAL.json';f=json.loads(fpath.read_text());f['manifest_sha256']=sha(mpath.read_bytes());fpath.write_text(json.dumps(f,indent=2)+'\n')
        cmd=['python','-B',str(r/'packet/public/verify.py'),'--root',str(d),'--project',str(a.project)]
        for s in ('final','manifest','report'):cmd+=['--'+s+'-sha256',getattr(a,s+'_sha256')]
        out=subprocess.run(cmd,capture_output=True,text=True)
        ok=(out.returncode==0) if case=='baseline' else (out.returncode!=0)
        results.append(dict(case=case,expected_behavior=ok,returncode=out.returncode,stdout=out.stdout,stderr=out.stderr))
    receipt={'cases':results,'all_expected':all(x['expected_behavior'] for x in results),'copies':str(base),'mathematical_gate':'none'}
    (work/'control-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert receipt['all_expected'],receipt
    print(json.dumps({'cases':len(results),'all_expected':True,'receipt':str(work/'control-receipt.json')}))


if __name__=='__main__':main()
