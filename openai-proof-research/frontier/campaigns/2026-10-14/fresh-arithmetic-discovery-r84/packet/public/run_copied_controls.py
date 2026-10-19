#!/usr/bin/env python3
"""Mutate disposable copies only. Integrity controls, never mathematics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',required=True)
p.add_argument('--tree',required=True)
p.add_argument('--finalhash',required=True)
p.add_argument('--reporthash',required=True)
a=p.parse_args()
r=Path(a.root).resolve()

def sha(b): return hashlib.sha256(b).hexdigest()
def fingerprint():
    result={}
    for f in sorted(r.rglob('*')):
        if f.relative_to(r).parts[0]=='controls': continue
        s=f.lstat()
        result[f.relative_to(r).as_posix()]=[s.st_mode,s.st_nlink,sha(f.read_bytes()) if f.is_file() else None]
    return result
before=fingerprint()
controls=r/'controls';controls.mkdir(exist_ok=True)
work=controls/'temporary-copy'
if work.exists(): raise SystemExit('refuse pre-existing temporary-copy')
verifier=r/'packet/public/verify.py'
rows=[]
cases=['baseline','missing-final-anchor','wrong-final-anchor','missing-report-anchor','wrong-report-anchor','changed-payload','missing-payload','extra-file','extra-directory','symlink','hardlink','changed-manifest','changed-report','changed-verifier','wrong-tree','coherent-reseal-old-anchor']
try:
    for name in cases:
        work.mkdir()
        shutil.copytree(r/'packet',work/'packet')
        for f in ['REPORT.md','MANIFEST.json','FINAL.json']:shutil.copyfile(r/f,work/f)
        target=work/'packet/public/research.md'
        cmd=[sys.executable,'-B',str(verifier),'--root',str(work),'--tree',str(Path(a.tree).resolve()),'--finalhash',a.finalhash,'--reporthash',a.reporthash]
        diagnostic=None
        if name=='missing-final-anchor':del cmd[cmd.index('--finalhash'):cmd.index('--finalhash')+2];diagnostic='--finalhash'
        elif name=='wrong-final-anchor':cmd[cmd.index('--finalhash')+1]='0'*64;diagnostic='detached FINAL mismatch'
        elif name=='missing-report-anchor':del cmd[cmd.index('--reporthash'):cmd.index('--reporthash')+2];diagnostic='--reporthash'
        elif name=='wrong-report-anchor':cmd[cmd.index('--reporthash')+1]='0'*64;diagnostic='detached REPORT mismatch'
        elif name=='changed-payload':target.write_bytes(target.read_bytes()+b'changed');diagnostic='payload bytes mismatch'
        elif name=='missing-payload':target.unlink();diagnostic='file membership mismatch'
        elif name=='extra-file':(work/'packet/unlisted.txt').write_text('extra');diagnostic='file membership mismatch'
        elif name=='extra-directory':(work/'packet/unlisted').mkdir();diagnostic='directory membership mismatch'
        elif name=='symlink':target.unlink();target.symlink_to('geometry.md');diagnostic='single-link regular file'
        elif name=='hardlink':target.unlink();os.link(work/'packet/public/geometry.md',target);diagnostic='single-link regular file'
        elif name=='changed-manifest':(work/'MANIFEST.json').write_bytes((work/'MANIFEST.json').read_bytes()+b' ');diagnostic='manifest mismatch'
        elif name=='changed-report':(work/'REPORT.md').write_bytes((work/'REPORT.md').read_bytes()+b'changed');diagnostic='detached REPORT mismatch'
        elif name=='changed-verifier':(work/'packet/public/verify.py').write_bytes((work/'packet/public/verify.py').read_bytes()+b'\n# changed\n');diagnostic='verifier mismatch'
        elif name=='wrong-tree':
            tree=work/'wrong-tree.json';tree.write_text('{}');cmd[cmd.index('--tree')+1]=str(tree);diagnostic='external complete tree mismatch'
        elif name=='coherent-reseal-old-anchor':
            target.write_bytes(target.read_bytes()+b'changed')
            mf=json.loads((work/'MANIFEST.json').read_text());mf['files']['public/research.md']={'sha256':sha(target.read_bytes()),'bytes':target.stat().st_size};(work/'MANIFEST.json').write_text(json.dumps(mf,indent=2)+'\n')
            ff=json.loads((work/'FINAL.json').read_text());ff['manifest_sha256']=sha((work/'MANIFEST.json').read_bytes());(work/'FINAL.json').write_text(json.dumps(ff,indent=2)+'\n');diagnostic='detached FINAL mismatch'
        q=subprocess.run(cmd,capture_output=True,text=True)
        ok=q.returncode==0 if name=='baseline' else q.returncode!=0 and diagnostic in q.stderr
        rows.append({'case':name,'expected_accept':name=='baseline','returncode':q.returncode,'expected_diagnostic':diagnostic,'stdout':q.stdout,'stderr':q.stderr,'as_expected':ok})
        shutil.rmtree(work)
        if not ok: raise RuntimeError('unexpected control outcome '+name)
finally:
    if work.exists():shutil.rmtree(work)
after=fingerprint()
result={'scope':'integrity only; no mathematical gate','original_unchanged':before==after,'original_before_sha256':sha(json.dumps(before,sort_keys=True).encode()),'original_after_sha256':sha(json.dumps(after,sort_keys=True).encode()),'controls':rows}
(controls/'results.json').write_text(json.dumps(result,indent=2)+'\n')
if before!=after:raise SystemExit('original changed')
print(json.dumps({'cases':len(rows),'all_expected':all(x['as_expected'] for x in rows),'original_unchanged':True,'results_sha256':sha((controls/'results.json').read_bytes())}))
