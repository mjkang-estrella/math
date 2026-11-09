#!/usr/bin/env python3
"""Run from a fresh extracted packet; no local oleans or ambient Lean paths."""
from pathlib import Path
import os,json,hashlib,subprocess,sys
root=Path(__file__).resolve().parent.parent
os.chdir(root)
pins=json.loads((root/'pins.json').read_text())
leanbin=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
assert hashlib.sha256((leanbin/'lean').read_bytes()).hexdigest()==pins['lean_binary_sha256']
base=Path(pins['cache'])
assert hashlib.sha256((base/'mathlib/.lake/build/lib/lean/Mathlib.olean').read_bytes()).hexdigest()==pins['mathlib_root_olean_sha256']
for p in root.rglob('*.olean'): p.unlink()
logs=root/'replay-logs';logs.mkdir(exist_ok=True)
env={'PATH':str(leanbin)+':/usr/bin:/bin','LEAN_PATH':':'.join([str(root)]+[str(d/'.lake/build/lib/lean') for d in sorted(base.iterdir()) if d.is_dir()]),'MALLOC_ARENA_MAX':'2','OMP_NUM_THREADS':'2','OPENBLAS_NUM_THREADS':'2','LANG':'C.UTF-8'}
modules=['Sigma.Basic','Sigma.Identity','Sigma.Attainment','Sigma.PathExtension']
commands=[]
for m in modules:
 f=m.replace('.','/')
 commands.append((m+'-build',['lean','-j1','-DwarningAsError=true','-o',f+'.olean',f+'.lean']))
 commands.append((m+'-checker',['leanchecker',m]))
commands += [('audit',['lean','-j1','-DwarningAsError=true','Audit.lean']),('negative-controls',['lean','-j1','-DwarningAsError=true','NegativeControls.lean'])]
results=[]
for label,cmd in commands:
 with (logs/(label+'.log')).open('w') as out:
  r=subprocess.run([sys.executable,'scripts/capped.py']+cmd,env=env,stdout=out,stderr=subprocess.STDOUT)
 results.append({'label':label,'command':cmd,'exit':r.returncode})
 print(label,r.returncode,flush=True)
 if r.returncode: break
(root/'replay-results.json').write_text(json.dumps(results,indent=2)+'\n')
assert len(results)==len(commands) and all(r['exit']==0 for r in results)
