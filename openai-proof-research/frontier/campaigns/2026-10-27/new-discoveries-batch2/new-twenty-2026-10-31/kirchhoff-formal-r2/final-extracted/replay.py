#!/usr/bin/env python3
"""Strict source-only replay; execute with python3 -I replay.py."""
from pathlib import Path
import os,sys,json,subprocess,hashlib
D=Path(__file__).resolve().parent
if any(D.rglob('*.olean')):
 raise SystemExit('Refusing existing oleans: extract the source-only packet into a new directory.')
lean=os.environ.get('LEAN_BIN'); packages=os.environ.get('LEAN_PACKAGES')
if not lean or not packages:raise SystemExit('Set LEAN_BIN and LEAN_PACKAGES.')
for p in ['logs','receipts','outputs']:(D/p).mkdir(exist_ok=True)
env={'PATH':str(Path(lean).parent)+':/usr/bin:/bin','HOME':str(D),'TMPDIR':str(D/'outputs'),'MALLOC_ARENA_MAX':'2','LEAN_BIN':lean,'LEAN_PACKAGES':packages,'PYTHONDONTWRITEBYTECODE':'1'}
manifest=json.loads((D/'source-hashes.json').read_text())
for f,h in manifest.items():
 if hashlib.sha256((D/f).read_bytes()).hexdigest()!=h:raise SystemExit('Source hash mismatch: '+f)
def run(name,args,success=True):
 e=dict(env,RUN_NAME=name)
 r=subprocess.run([sys.executable,'-I',str(D/'scripts/run.py')]+args,cwd=D,env=e,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (D/'logs'/f'{name}-driver.log').write_text(r.stdout)
 receipt=json.loads((D/'receipts'/f'{name}.json').read_text())
 if receipt['killed'] or (success and r.returncode!=0) or (not success and r.returncode==0):raise SystemExit('Unexpected result: '+name+'\n'+r.stdout[-3000:])
 if not success and 'error:' not in (D/'logs'/f'{name}.log').read_text():raise SystemExit('Negative control did not produce a Lean error: '+name)
 print(name+': '+('PASS' if success else 'REJECTED AS REQUIRED'),flush=True)
run('version',['--version'])
for m in ['Basic','Certificates','Graph','RealBridge']:
 run('strict-'+m,['-o',m+'.olean',m+'.lean'])
for m in ['Basic','Certificates','Graph','RealBridge']:
 run('leanchecker-'+m,['--checker',m])
run('audit',['Audit.lean'])
for m in ['WrongMPValue','GroupAsMP','Perturbed']:
 run('negative-'+m,['../negative/'+m+'.lean'],False)
log=(D/'logs/audit.log').read_text();import re
count=int(re.search(r'AUDITED_LOCAL_DECLARATIONS\|(\d+)',log).group(1))
summary={'status':'strict replay passed; root acceptance pending','all_local_declarations':count,'negative_controls':3,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'source_hashes':manifest}
(D/'receipts/replay.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
