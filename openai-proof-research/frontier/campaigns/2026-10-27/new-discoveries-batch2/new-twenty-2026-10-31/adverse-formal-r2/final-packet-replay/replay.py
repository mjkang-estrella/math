#!/usr/bin/env python3
"""Run inside an empty source extraction. Requires LEAN_BIN and LEAN_PACKAGES."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,gzip,shutil
root=Path(__file__).resolve().parent
os.chdir(root)
if list(root.rglob('*.olean')) or list(root.rglob('*.olean.private')) or list(root.rglob('*.olean.server')):
 raise SystemExit('REFUSED: existing oleans in source extraction')
for d in ('logs','receipts','tmp','negative'):(root/d).mkdir(exist_ok=True)
lean=Path(os.environ['LEAN_BIN']); lean=lean/'lean' if lean.is_dir() else lean
packages=Path(os.environ['LEAN_PACKAGES'])
assert lean.is_file() and packages.is_dir()
env=os.environ.copy()
env.update(LEAN_BIN=str(lean.parent),LEAN_PACKAGES=str(packages),LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2',TMPDIR=str(root/'tmp'),PYTHONDONTWRITEBYTECODE='1')
# Deliberately discard inherited search paths and build only in this extraction.
for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_PLUGIN_PATH','LD_PRELOAD','LEAN_OPTS']:env.pop(k,None)
mods=['Definitions','Certificates','Gram','Independence']+[f'Deletion{i}' for i in range(6)]+['Bridges','Quadratic','Main']
def run(script,label,args,ok=True):
 p=subprocess.run(['sh',str(root/'scripts'/script),label]+args,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (root/'logs'/f'{label}.driver.log').write_text(p.stdout)
 if (p.returncode==0)!=ok:raise RuntimeError(f'{label}: unexpected exit {p.returncode}; see logs')
 return json.loads((root/'receipts'/f'{label}.json').read_text())
receipts=[]
for m in mods:
 receipts.append(run('lean.sh','replay-'+m,['-o',f'formal/{m}.olean',f'formal/{m}.lean']))
 receipts.append(run('checker.sh','checker-'+m,[m]))
receipts.append(run('lean.sh','full-audit',['-o','formal/Audit.olean','formal/Audit.lean']))
# The audit output contains the entire expression trees, including generated declarations.
count=None
with (root/'logs/full-audit.log').open() as f:
 for line in f:
  if line.startswith('AUDIT_COUNT '):count=int(line.split()[1])
assert count and count>100
with (root/'logs/full-audit.log').open('rb') as src,gzip.open(root/'logs/full-audit.log.gz','wb') as dst:shutil.copyfileobj(src,dst)
(root/'logs/full-audit.log').unlink()
neg=[]
controls={
 'wrong-alpha':'import Main\nopen Adverse381433\nexample : alpha latinGraph = 6 := by exact alpha_eq_five\n',
 'wrong-upsilon':'import Main\nopen Adverse381433\nexample : upsilon latinGraph = 5 := by exact global_upsilon\n',
 'wrong-eigenvalue':'import Main\nopen Adverse381433\nexample : leastEigenvalue latinGraph = -2 := by exact global_least\n',
 'wrong-adjacency':'import Main\nopen Adverse381433\nexample : ¬latinGraph.Adj (0,0) (0,1) := by unfold latinGraph; decide\n',
}
# These are derived source mutations, never edits to the read-only evidence copies.
cert=(root/'formal/Certificates.lean').read_text()
controls['corrupt-fractional']=cert.replace('![1,0,0,0,0,0,0,1/4','![0,0,0,0,0,0,0,1/4',1)
controls['corrupt-kernel']=cert.replace('0,0,-1,1,0,0,0,1,0,-1','0,0,0,1,0,0,0,1,0,-1',1)
for name,src in controls.items():
 file=f'negative/{name}.lean';(root/file).write_text(src)
 r=run('lean.sh','negative-'+name,[file],False)
 assert r['termination'] is None and r['exit']==1
 assert 'error' in (root/'logs'/f'negative-{name}.log').read_text()
 neg.append({'control':name,'rejected':True,'receipt':r})
# Driver freshness refusal is also exercised after the build.
p=subprocess.run([sys.executable,'-I',str(root/'replay.py')],env=env,capture_output=True,text=True)
assert p.returncode!=0 and 'REFUSED: existing oleans' in p.stderr
(root/'logs/freshness-negative.log').write_text(p.stdout+p.stderr)
(root/'receipts/negative-controls.json').write_text(json.dumps(neg,indent=2)+'\n')
report={'strict_fresh_replay':'pass','leanchecker_modules':mods,'declaration_count':count,'negative_controls':len(neg)+1,'source_hashes':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (root/'formal').glob('*.lean')},'calls':receipts}
(root/'receipts/replay.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('calls','source_hashes')},indent=2))
